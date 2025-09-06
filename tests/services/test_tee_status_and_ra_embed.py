#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_tee_status_and_ra_embed.py       |
# | ROLE: Enterprise tests: TEE status + RA embedding on PUBLISH |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from fastapi.testclient import TestClient

from services.api_gateway.main import app as gateway_app
from services.proofgate.app import app as proofgate_app


def _write_attestation(tmp: Path) -> Path:
    att = {
        "vendor": "intel",
        "product": "sgx",
        "claims": {"mr_enclave": "abc", "mr_signer": "def", "prod_id": 1},
    }
    p = tmp / "attestation.json"
    p.write_text(json.dumps(att), encoding="utf-8")
    return p


def _base_pco() -> dict[str, Any]:
    return {
        "domain": "lex",
        "case_id": "CER-TEE-EMBED-1",
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
        "sources": [
            {
                "id": "s1",
                "uri": "hash://sha256/aa",
                "digest": "a" * 64,
                "retrieved_at": "2025-01-01T00:00:00Z",
            }
        ],
        "derivations": [
            {
                "claim_id": "c1",
                "solver": "z3",
                "proof_format": "LFSC",
                "artifact_digest": "b" * 64,
            }
        ],
        "reproducibility": {
            "image": "img:dev",
            "image_digest": "sha256:deadbeef",
            "seed": "0",
        },
        "signatures": [
            {
                "role": "producer",
                "alg": "ed25519",
                "key_id": "kid1",
                "signature": "sig1",
            },
            {
                "role": "counsel",
                "alg": "ed25519",
                "key_id": "kid2",
                "signature": "sig2",
            },
        ],
    }


def test_tee_status_reports_bunker_and_ra(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("BUNKER", "1")
    att = _write_attestation(tmp_path)
    monkeypatch.setenv("BUNKER_ATTESTATION_PATH", str(att))
    c = TestClient(gateway_app)
    r = c.get("/v1/tee/status")
    r.raise_for_status()
    body = r.json()
    assert body.get("bunker_on") is True
    assert body.get("attested") is True
    ra = body.get("ra") or {}
    assert isinstance(ra.get("vendor"), str) and isinstance(ra.get("product"), str)
    assert isinstance(ra.get("measurement"), str) and len(ra.get("measurement")) == 64


def test_publish_embeds_ra_when_bunker_on(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("BUNKER", "1")
    att = _write_attestation(tmp_path)
    monkeypatch.setenv("BUNKER_ATTESTATION_PATH", str(att))
    # Ensure no strict RA require for this test
    monkeypatch.delenv("TEE_RA_REQUIRE", raising=False)
    c = TestClient(proofgate_app)
    pco = _base_pco()
    # Add minimal TEE attestation info to PCO as expected by bunker mode
    pco["tee"] = {"attested": True}
    r = c.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
    r.raise_for_status()
    body = r.json()
    assert body["status"] == "PUBLISH"
    out = body.get("pco") or {}
    # RA embedded into PCO under tee.ra
    tee = out.get("tee") or {}
    assert tee.get("attested") is True
    ra = tee.get("ra") or {}
    assert isinstance(ra.get("vendor"), str) and isinstance(ra.get("product"), str)
    assert isinstance(ra.get("measurement"), str) and len(ra.get("measurement")) == 64
