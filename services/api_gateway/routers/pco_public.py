#!/usr/bin/env python3
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | MODULE / MODUŁ: services/api_gateway/routers/pco_public.py          |
# | DATA: 2025-08-19                                                    |
# +=====================================================================+
# | ROLA:                                                               |
# |  EN: Public PCO (zero PII). Verifies Merkle (MVP/real) + Ed25519.   |
# |  PL: Publiczny PCO (0 PII). Weryfikuje Merkle (MVP/real) + Ed25519. |
# +=====================================================================+

from __future__ import annotations

# stdlib
import hashlib
import json
import os
from pathlib import Path
from typing import Any

# third-party
from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, Field, field_validator

# core (kanoniczne funkcje i crypto)
from core.pco.crypto import (
    b64u_encode,
    canonical_bundle_hash_hex,
    canonical_digest_hex,
    compute_leaf_hex,
    ed25519_verify_b64u,
    load_pubkey_bytes_from_env,
    sha256_hex,
)

router = APIRouter(prefix="/pco/public", tags=["pco"])


# ──────────────────────────────────────────────────────────────────────────────
# Pomocnicze aliasy 1:1 pod testy (nie zmieniaj nazw)
# tests/test_pco_public.py importuje te symbole z tego modułu
def _hex(s: str) -> str:
    """SHA-256 hex of UTF-8 text (alias pod testy)."""
    return sha256_hex(s)


def _b64u(data: bytes) -> str:
    """Base64URL bez '=' (alias pod testy)."""
    return b64u_encode(data)


def _bundle_hash_hex(smt2_hash_hex: str, lfsc_text: str, drat_text: str | None = None) -> str:
    """Alias pod testy → wywołuje kanoniczną funkcję."""
    return canonical_bundle_hash_hex(smt2_hash_hex, lfsc_text, drat_text)


def _canonical_digest_hex(pub: dict[str, Any], merkle_root_hex: str) -> str:
    """Alias pod testy → wywołuje kanoniczną funkcję."""
    return canonical_digest_hex(
        rid=str(pub["rid"]),
        smt2_hash_hex=str(pub["smt2_hash"]),
        lfsc_text=str(pub.get("lfsc", "")),
        drat_text=str(pub["drat"]) if pub.get("drat") is not None else None,
        merkle_root_hex=merkle_root_hex,
    )


# ──────────────────────────────────────────────────────────────────────────────
# zero-PII: prosta denylista kluczy
FORBIDDEN_KEYS = {
    "name",
    "first_name",
    "last_name",
    "pesel",
    "email",
    "phone",
    "address",
    "dob",
    "ssn",
    "patient_id",
    "person_id",
    "user_id",
    "ip",
    "session_id",
    "headers",
}

DEFAULT_BUNDLE_DIR_FALLBACK = Path("./data/public_pco")


def _bundle_dir() -> Path:
    """Resolve bundle dir at call time, honoring current ENV."""
    return Path(os.getenv("PROOF_BUNDLE_DIR") or DEFAULT_BUNDLE_DIR_FALLBACK)


# ──────────────────────────────────────────────────────────────────────────────
# MODELE
class MerkleStep(BaseModel):
    sibling: str  # hex
    dir: str  # "L" or "R"


class PublicPCO(BaseModel):
    rid: str = Field(..., min_length=3)
    smt2_hash: str = Field(..., min_length=64, max_length=64)  # hex sha256 of SMT2
    lfsc: str = Field(..., min_length=2)  # LFSC (plain text)
    drat: str | None = None  # DRAT (plain text, optional)
    merkle_proof: list[MerkleStep] = Field(default_factory=list)  # list or empty
    signature: str = Field(..., min_length=40)  # detached (base64url, bez '=')

    @field_validator("smt2_hash")
    @classmethod
    def _hex64(cls, v: str) -> str:
        int(v, 16)  # raises on invalid hex
        return v.lower()


# ──────────────────────────────────────────────────────────────────────────────
# MERKLE helpers
def _h(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()


def _apply_merkle_path(leaf_hex: str, path: list[MerkleStep]) -> str:
    # Pusta ścieżka ⇒ root == leaf (dokładnie jak w teście)
    if not path:
        return leaf_hex.lower()
    cur = bytes.fromhex(leaf_hex)
    for step in path:
        sib = bytes.fromhex(step.sibling)
        if step.dir == "L":
            cur = _h(sib + cur)
        elif step.dir == "R":
            cur = _h(cur + sib)
        else:
            raise HTTPException(status_code=400, detail=f"Invalid merkle step.dir: {step.dir}")
    return cur.hex()


def _parse_merkle_proof(raw: object) -> list[MerkleStep]:
    """
    Akceptuj:
      • [] (MVP)
      • [{"sibling":..., "dir":"L|R"}]
      • {"path":[...]} (zgodność wstecz)
      • alias 'position' ≡ 'dir'
    """
    if raw is None:
        return []
    if isinstance(raw, dict) and "path" in raw:
        raw = raw["path"]
    if isinstance(raw, list):
        norm: list[MerkleStep] = []
        for step in raw:
            if isinstance(step, MerkleStep):  # już zparsowany
                norm.append(step)
                continue
            if not isinstance(step, dict):
                raise HTTPException(status_code=400, detail="Invalid merkle step type")
            d = step.get("dir") or step.get("position")
            sib = step.get("sibling")
            if d not in ("L", "R"):
                raise HTTPException(
                    status_code=400,
                    detail="Invalid merkle step.dir/position",
                )
            if not isinstance(sib, str) or not sib:
                raise HTTPException(
                    status_code=400,
                    detail="Invalid merkle step: missing 'sibling'",
                )
            norm.append(MerkleStep(sibling=sib, dir=str(d)))
        return norm
    raise HTTPException(status_code=400, detail="merkle_proof must be list or {path:[...] }")


# ──────────────────────────────────────────────────────────────────────────────
# STORAGE
def _bundle_path(rid: str) -> Path:
    return _bundle_dir() / f"{rid}.json"


def _load_public_bundle_from_fs(rid: str) -> dict[str, Any]:
    p = _bundle_path(rid)
    if not p.exists():
        raise HTTPException(status_code=404, detail="PCO bundle not found")
    try:
        raw = p.read_text(encoding="utf-8")
        data = json.loads(raw)
        if not isinstance(data, dict):
            raise ValueError("Bundle is not an object")
        return data
    except Exception as e:  # pragma: no cover
        raise HTTPException(status_code=500, detail=f"Cannot read bundle: {e}") from e


# ──────────────────────────────────────────────────────────────────────────────
# PII
def _assert_no_pii(bundle: dict[str, Any]) -> None:
    bad = sorted(set(bundle.keys()) & FORBIDDEN_KEYS)
    if bad:
        raise HTTPException(status_code=422, detail=f"PII field(s) present: {bad}")


# ──────────────────────────────────────────────────────────────────────────────
# ENTRYPOINT
@router.get("/{rid}", response_model=PublicPCO)
def get_public_pco(rid: str, request: Request) -> PublicPCO:
    """
    EN/PL: Returns public PCO; validates zero-PII, Merkle proof, and Ed25519 signature.
    """
    pub = _load_public_bundle_from_fs(rid)
    _assert_no_pii(pub)

    # 1) Bundle hash → leaf → merkle root
    bundle_hash_hex = _bundle_hash_hex(
        str(pub["smt2_hash"]),
        str(pub.get("lfsc", "")),
        str(pub["drat"]) if pub.get("drat") is not None else None,
    )
    leaf_hex = compute_leaf_hex(str(pub["rid"]), bundle_hash_hex)
    path = _parse_merkle_proof(pub.get("merkle_proof"))
    merkle_root_hex = _apply_merkle_path(leaf_hex, path)

    # 2) Canonical digest (dokładnie jak w testach)
    digest_hex = _canonical_digest_hex(pub, merkle_root_hex)

    # 3) Ed25519 (detached, base64url) nad bytes.fromhex(digest_hex)
    try:
        ed25519_verify_b64u(
            load_pubkey_bytes_from_env(),
            str(pub["signature"]),
            digest_hex,
        )
    except Exception as e:
        # nie ujawniamy szczegółów kryptograficznych na zewnątrz
        raise HTTPException(status_code=400, detail="Invalid signature") from e

    # Pydantic dodatkowo sanityzuje typy/formaty
    return PublicPCO(**{**pub, "merkle_proof": path})
