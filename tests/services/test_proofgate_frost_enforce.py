#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_proofgate_frost_enforce.py       |
# | ROLE: Project test module.                                  |
# | PLIK: tests/services/test_proofgate_frost_enforce.py       |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: FROST 2‑z‑3 — enforce w publish (opcjonalny przez ENV), zapis quorum w PCO/ledger.
EN: FROST 2‑of‑3 — enforce in publish (opt-in via ENV), quorum presence in PCO/ledger.
"""

from __future__ import annotations

from typing import Any

from fastapi.testclient import TestClient

from security.frost import aggregate
from services.ledger_service.ledger import compute_provenance_hash, ledger_service
from services.proofgate.app import app


def _base_ok_pco() -> dict[str, Any]:
    return {
        "domain": "lex",
        "case_id": "CER-LEX-FROST-1",
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


def test_publish_without_frost_env_ignores_quorum_requirement(monkeypatch) -> None:
    monkeypatch.delenv("REQUIRE_COSIGN_ATTESTATIONS", raising=False)
    monkeypatch.delenv("FROST_REQUIRE", raising=False)
    c = TestClient(app)
    pco = _base_ok_pco()
    r = c.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
    assert r.status_code == 200
    assert r.json()["status"] == "PUBLISH"


def test_publish_with_frost_env_requires_quorum(monkeypatch) -> None:
    # Enable FROST gate
    monkeypatch.setenv("REQUIRE_COSIGN_ATTESTATIONS", "1")
    c = TestClient(app)
    # Missing quorum → ABSTAIN
    pco_bad = _base_ok_pco()
    r1 = c.post("/v1/proofgate/publish", json={"pco": pco_bad, "budget_tokens": 10})
    assert r1.status_code == 200
    assert r1.json()["status"] == "ABSTAIN"
    # Provide quorum (2-of-3)
    pco_ok = _base_ok_pco()
    fq = aggregate(["kidA", "kidB"], threshold=2, participants=3)
    pco_ok["cosign"] = fq.to_dict()
    r2 = c.post("/v1/proofgate/publish", json={"pco": pco_ok, "budget_tokens": 10})
    assert r2.status_code == 200
    body = r2.json()
    assert body["status"] == "PUBLISH"
    # Ledger includes hash of PCO containing quorum (stabilize by recomputation)
    expect_hash = compute_provenance_hash(pco_ok, include_timestamp=False)
    recs = ledger_service.get_records_for_case(case_id=pco_ok["case_id"])
    assert any(
        r.get("type") == "PCO_PUBLISH" and r.get("document_hash") == expect_hash
        for r in recs
    )
