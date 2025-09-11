#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/pco_public.py          |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/pco_public.py          |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla obszaru publiczne PCO i JWKS.

EN: FastAPI router for public PCO and JWKS.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import hashlib
import json
import os
import re
from pathlib import Path
from typing import Any

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, ConfigDict, Field, field_validator

from core.pco.crypto import (b64u_encode, canonical_bundle_hash_hex,
                             canonical_digest_hex, compute_leaf_hex,
                             ed25519_verify_b64u, load_pubkey_bytes_from_env,
                             sha256_hex)

# === KONFIGURACJA / CONFIGURATION ===

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

# === MODELE / MODELS ===


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

    # OpenAPI example for documentation
    model_config = ConfigDict(
        json_schema_extra={
            "example": {
                "rid": "demo-001",
                "smt2_hash": "d" * 64,
                "lfsc": "(proof ...)\n",
                "drat": None,
                "merkle_proof": [],
                "signature": "SGVsbG9TaWduYXR1cmU",  # base64url stub
            }
        }
    )


# === LOGIKA / LOGIC ===

DEFAULT_BUNDLE_DIR_FALLBACK = Path("./data/public_pco")

# stdlib

# third-party

# core (kanoniczne funkcje i crypto)

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


def _bundle_dir() -> Path:
    """Resolve bundle dir at call time, honoring current ENV."""

    return Path(os.getenv("PROOF_BUNDLE_DIR") or DEFAULT_BUNDLE_DIR_FALLBACK)


# ──────────────────────────────────────────────────────────────────────────────

# MODELE

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
    # Sanitize rid to prevent path traversal
    sanitized_rid = re.sub(r'[^a-zA-Z0-9_-]', '', rid.strip())
    if not sanitized_rid:
        raise HTTPException(status_code=400, detail="Invalid resource ID")

    # Ensure the final path is within the bundle directory
    bundle_dir = _bundle_dir()
    candidate_path = bundle_dir / f"{sanitized_rid}.json"

    # Resolve and check if it's within the allowed directory
    try:
        resolved_path = candidate_path.resolve()
        bundle_dir_resolved = bundle_dir.resolve()
        if not str(resolved_path).startswith(str(bundle_dir_resolved)):
            raise HTTPException(status_code=400, detail="Invalid path")
        return resolved_path
    except (OSError, ValueError):
        raise HTTPException(status_code=400, detail="Invalid path")


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

# === I/O / ENDPOINTS ===


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


# Kontrakt OpenAPI (docs/api/openapi.yaml) używa nazwy parametru "case_id".
# Zachowując główny endpoint zgodny z testami (/pco/public/{rid}),
# wystawiamy alias ścieżki z nazwą {case_id} wskazujący na tę samą logikę.


@router.get("/{case_id}", response_model=PublicPCO, include_in_schema=True)
def get_public_pco_by_case_id(case_id: str, request: Request) -> PublicPCO:  # pragma: no cover (alias)
    return get_public_pco(case_id, request)


# Alias ścieżki: zgodność z dokumentacją /pco/public/{case_id}
@router.get("/{case_id}", response_model=PublicPCO, include_in_schema=True)
def get_public_pco_alias(case_id: str, request: Request) -> PublicPCO:  # pragma: no cover - alias
    return get_public_pco(case_id, request)


# === TESTY / TESTS ===
