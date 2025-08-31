#!/usr/bin/env python3
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | MODULE / MODUŁ: services/api_gateway/routers/pco_bundle.py          |
# | DATE / DATA: 2025-08-31                                             |
# +=====================================================================+
# | ROLE / ROLA: Minimalny endpoint /v1/pco/bundle (walidacja + zapis)  |
# +=====================================================================+

from __future__ import annotations

import base64
import hashlib
import json
import os
from pathlib import Path
import time
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi import APIRouter, HTTPException, Request
from jsonschema import Draft202012Validator
from pydantic import BaseModel, Field, field_validator

from core.pco.crypto import canonical_bundle_hash_hex, canonical_digest_hex, compute_leaf_hex
from monitoring.metrics_slo import (
    certeus_compile_duration_ms,
    certeus_proof_verification_failed_total,
)
from services.api_gateway.limits import enforce_limits

router = APIRouter(prefix="/v1/pco", tags=["pco"])


class MerkleStep(BaseModel):
    sibling: str
    dir: str  # "L" | "R"


class PublicBundleIn(BaseModel):
    rid: str = Field(..., min_length=1)
    smt2_hash: str = Field(..., min_length=64, max_length=64)
    lfsc: str = Field(..., min_length=2)
    drat: str | None = None
    merkle_proof: list[MerkleStep] | dict | None = Field(default=None)
    smt2: str | None = None

    @field_validator("smt2_hash")
    @classmethod
    def _hx64(cls, v: str) -> str:
        int(v, 16)
        return v.lower()


def _bundle_dir() -> Path:
    return Path(os.getenv("PROOF_BUNDLE_DIR") or "./data/public_pco")


def _parse_merkle_proof(raw: object) -> list[MerkleStep]:
    if raw is None:
        return []
    if isinstance(raw, dict) and "path" in raw:
        raw = raw["path"]
    if isinstance(raw, list):
        norm: list[MerkleStep] = []
        for step in raw:
            if isinstance(step, MerkleStep):
                norm.append(step)
                continue
            if not isinstance(step, dict):
                raise HTTPException(status_code=400, detail="Invalid merkle step type")
            d = step.get("dir") or step.get("position")
            sib = step.get("sibling")
            if d not in ("L", "R"):
                raise HTTPException(status_code=400, detail="Invalid merkle step.dir/position")
            if not isinstance(sib, str) or not sib:
                raise HTTPException(status_code=400, detail="Invalid merkle step: missing 'sibling'")
            norm.append(MerkleStep(sibling=sib, dir=str(d)))
        return norm
    raise HTTPException(status_code=400, detail="merkle_proof must be list or {path:[...] }")


def _apply_merkle_path(leaf_hex: str, path: list[MerkleStep]) -> str:
    if not path:
        return leaf_hex.lower()
    cur = bytes.fromhex(leaf_hex)
    for step in path:
        sib = bytes.fromhex(step.sibling)
        if step.dir == "L":
            cur = hashlib.sha256(sib + cur).digest()
        elif step.dir == "R":
            cur = hashlib.sha256(cur + sib).digest()
        else:
            raise HTTPException(status_code=400, detail=f"Invalid merkle step.dir: {step.dir}")
    return cur.hex()


def _load_private_key_from_pem() -> Ed25519PrivateKey:
    pem_env = os.getenv("ED25519_PRIVKEY_PEM")
    if pem_env and "BEGIN" in pem_env:
        key_any = serialization.load_pem_private_key(pem_env.encode("utf-8"), password=None)
        if not isinstance(key_any, Ed25519PrivateKey):
            raise HTTPException(status_code=500, detail="PEM from env is not Ed25519 private key")
        return key_any
    pem_path = os.getenv("ED25519_PRIVKEY_PEM_PATH") or os.getenv("ED25519_PRIVKEY_PEM")
    if pem_path and Path(pem_path).exists():
        key_any = serialization.load_pem_private_key(Path(pem_path).read_bytes(), password=None)
        if not isinstance(key_any, Ed25519PrivateKey):
            raise HTTPException(status_code=500, detail="PEM file is not an Ed25519 private key")
        return key_any
    raise HTTPException(status_code=500, detail="Missing ED25519_PRIVKEY_PEM or *_PATH")


def _pb_schema_path() -> Path:
    # routers/ -> api_gateway/ -> schemas/
    return Path(__file__).resolve().parents[1] / "schemas" / "proofbundle_v0.2.json"


def _load_pb_schema() -> dict[str, Any]:
    p = _pb_schema_path()
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception as e:  # pragma: no cover
        raise HTTPException(status_code=500, detail=f"Cannot load ProofBundle schema: {e}") from e


def _kid_from_pubkey(sk: Ed25519PrivateKey) -> str:
    pk = sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)
    return hashlib.sha256(pk).hexdigest()[:16]


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _build_proofbundle(
    payload: PublicBundleIn,
    merkle_root_hex: str,
    digest_hex: str,
    signature_b64u: str,
    sk: Ed25519PrivateKey,
    *,
    status: str = "PENDING",
) -> dict[str, Any]:
    # Minimal, ale zgodny ze schematem ProofBundle v0.2 (z polami domyślnymi)
    # Zachowujemy spójność z istniejącym public payloadem: będziemy zapisywać oba zestawy pól.
    jurisdiction_country = os.getenv("DEFAULT_JURIS_COUNTRY", "PL")
    jurisdiction_domain = os.getenv("DEFAULT_JURIS_DOMAIN", "other")
    image = os.getenv("CERTEUS_IMAGE", "certeus/local:dev")
    image_digest = os.getenv("CERTEUS_IMAGE_DIGEST", "sha256:placeholder")
    seed = os.getenv("CERTEUS_SEED", "0")

    # sources: pseudo-URI oparty o hash SMT2
    src = {
        "id": "smt2",
        "uri": f"hash://sha256/{payload.smt2_hash}",
        "digest": payload.smt2_hash,
        "retrieved_at": _now_iso(),
        "license": "unknown",
    }

    # derivations: LFSC (+ opcjonalnie DRAT)
    derivs: list[dict[str, Any]] = [
        {
            "claim_id": "claim-1",
            "solver": "z3",
            "proof_format": "LFSC",
            "artifact_digest": hashlib.sha256(payload.lfsc.encode("utf-8")).hexdigest(),
        }
    ]
    if payload.drat is not None:
        derivs.append(
            {
                "claim_id": "claim-1",
                "solver": "z3",
                "proof_format": "DRAT",
                "artifact_digest": hashlib.sha256(payload.drat.encode("utf-8")).hexdigest(),
            }
        )

    pb: dict[str, Any] = {
        "version": "0.2",
        "case_id": payload.rid,
        "created_at": _now_iso(),
        "jurisdiction": {"country": jurisdiction_country, "domain": jurisdiction_domain},
        "claims": [
            {
                "id": "claim-1",
                "text": f"Auto-generated claim for rid={payload.rid}",
                "legal_basis": {"statutes": [], "cases": []},
                "evidence_refs": [],
            }
        ],
        "sources": [src],
        "derivations": derivs,
        "risk": {"ece": 0.0, "brier": 0.0, "p95_latency_ms": 0, "abstain_rate": 0.0},
        "ledger": {"merkle_root": merkle_root_hex},
        "signatures": [
            {
                "role": "producer",
                "alg": "ed25519",
                "key_id": _kid_from_pubkey(sk),
                "signature": signature_b64u,
            }
        ],
        "reproducibility": {"image": image, "image_digest": image_digest, "seed": seed, "env": {}},
        "attachments": [],
        "status": status,
    }

    # Walidacja ze schematem
    schema = _load_pb_schema()
    Draft202012Validator(schema).validate(pb)
    return pb


@router.post("/bundle")
def create_bundle(payload: PublicBundleIn, request: Request) -> dict[str, Any]:
    enforce_limits(request, cost_units=3)

    path = _parse_merkle_proof(payload.merkle_proof)
    bundle_hash_hex = canonical_bundle_hash_hex(payload.smt2_hash, payload.lfsc, payload.drat)
    leaf_hex = compute_leaf_hex(payload.rid, bundle_hash_hex)
    merkle_root_hex = _apply_merkle_path(leaf_hex, path)

    digest_hex = canonical_digest_hex(
        rid=payload.rid,
        smt2_hash_hex=payload.smt2_hash,
        lfsc_text=payload.lfsc,
        drat_text=payload.drat,
        merkle_root_hex=merkle_root_hex,
    )

    sk = _load_private_key_from_pem()
    signature_b64u = base64.urlsafe_b64encode(sk.sign(bytes.fromhex(digest_hex))).rstrip(b"=").decode("ascii")

    out_obj: dict[str, Any] = {
        "rid": payload.rid,
        "smt2_hash": payload.smt2_hash,
        "lfsc": payload.lfsc,
        "merkle_proof": [step.model_dump() for step in path],
        "signature": signature_b64u,
        "issued_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if payload.drat is not None:
        out_obj["drat"] = payload.drat

    # Optional verification of SMT2 if provided; record SLO metrics
    pb_status = "PENDING"
    if getattr(payload, "smt2", None):
        t0 = time.perf_counter()
        try:
            from kernel.truth_engine import DualCoreVerifier  # type: ignore

            _ = DualCoreVerifier().verify(payload.smt2 or "", lang="smt2", case_id=payload.rid)
        except Exception:
            certeus_proof_verification_failed_total.inc()
            pb_status = "ABSTAIN"
        finally:
            try:
                certeus_compile_duration_ms.observe((time.perf_counter() - t0) * 1000.0)
            except Exception:
                pass

    # Zbuduj pełny ProofBundle wg schematu i dołącz do payloadu publicznego (kompatybilnie)
    try:
        proofbundle = _build_proofbundle(payload, merkle_root_hex, digest_hex, signature_b64u, sk, status=pb_status)
        out_obj.update(proofbundle)
    except Exception as e:
        # Gdyby walidacja padła, zgłoś błąd 400 (nie zapisujemy wadliwego bundle)
        raise HTTPException(status_code=400, detail=f"Invalid ProofBundle: {e}") from e

    out_dir = _bundle_dir()
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{payload.rid}.json"
    out_path.write_text(json.dumps(out_obj, ensure_ascii=False, indent=2), encoding="utf-8")

    return {
        "ok": True,
        "rid": payload.rid,
        "digest_hex": digest_hex,
        "signature": signature_b64u,
        "public_path": str(out_path),
    }
