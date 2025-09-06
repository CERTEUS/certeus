#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_proofgate_sec_pco_publish.py     |
# | ROLE: Project test module.                                  |
# | PLIK: tests/services/test_proofgate_sec_pco_publish.py     |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Kontrakt publikacji PCO z rozszerzeniem `security` (SEC‑PCO).
EN: Contract test for publishing PCO with `security` (SEC‑PCO) extension.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.ledger_service.ledger import ledger_service
from services.proofgate.app import app


def _base_ok_pco_with_security() -> dict:
    # Use domain 'lex' to avoid governance SEC publish restrictions when role enforcement is on
    return {
        "domain": "lex",
        "case_id": "CER-LEX-SECEXT-1",
        # Required for decision path → PUBLISH
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
        # Optional TEE attestation flag (passes when BUNKER=1)
        "tee": {"attested": True},
        # SEC‑PCO extension (validated when VALIDATE_PCO=1)
        "security": {
            "finding_id": "SEC-0001",
            "severity": "HIGH",
            "status": "OPEN",
            "controls": ["ISO27001:A.12.6"],
            "evidence": [
                {
                    "digest": "sha256:" + ("a" * 64),
                    "type": "artifact",
                    "uri": "pfs://mail/MSEC/rep.pdf",
                }
            ],
            "cwe": ["CWE-79"],
            "cve": ["CVE-2025-0001"],
            "cvss": 8.2,
        },
    }


def test_publish_with_security_extension(monkeypatch) -> None:
    # Ensure optional validation path is exercised (report-only)
    monkeypatch.setenv("VALIDATE_PCO", "1")
    client = TestClient(app)
    pco = _base_ok_pco_with_security()
    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
    assert r.status_code == 200, r.text
    body = r.json()
    assert body["status"] == "PUBLISH"
    # Ledger reference present
    assert isinstance(body.get("ledger_ref"), str) and len(body["ledger_ref"]) == 64
    # Ledger contains publish event for case
    records = ledger_service.get_records_for_case(case_id=pco["case_id"])
    assert any(
        rec.get("type") == "PCO_PUBLISH" and rec.get("chain_self") == body["ledger_ref"]
        for rec in records
    )


def test_publish_still_ok_when_security_extension_invalid_report_only(
    monkeypatch,
) -> None:
    # VALIDATE_PCO enables report-only validation; decision path should remain unaffected
    monkeypatch.setenv("VALIDATE_PCO", "1")
    client = TestClient(app)
    pco = _base_ok_pco_with_security()
    # Break SEC evidence (required) to trigger schema error
    if isinstance(pco.get("security"), dict):
        pco["security"].pop("evidence", None)  # type: ignore[index]
    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
    assert r.status_code == 200, r.text
    body = r.json()
    # Decision should still be PUBLISH because validation is report-only
    assert body["status"] == "PUBLISH"
