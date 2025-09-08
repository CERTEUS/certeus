#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/security/test_proof_only_coverage.py           |
# | ROLE: Validate Proof-Only coverage over protected routes     |
# +-------------------------------------------------------------+

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_proof_only_protected_endpoints_are_enforced(monkeypatch) -> None:
    # Enforce proof-only
    monkeypatch.setenv("STRICT_PROOF_ONLY", "1")
    c = TestClient(app)

    # Enumerate endpoints we consider protected (must be in sync with middleware)
    protected = [
        (
            "POST",
            "/v1/pco/bundle",
            {
                "rid": "RID-1",
                "smt2_hash": "0" * 64,
                "lfsc": "()",
                "merkle_proof": [],
                "smt2": "()",
            },
        ),
        (
            "POST",
            "/v1/proofgate/publish",
            {
                "pco": {"case_id": "CER-SEC-1"},
                "budget_tokens": 1,
            },
        ),
    ]

    enforced = 0
    for method, path, body in protected:
        if method == "POST":
            r = c.post(path, json=body)
        else:
            r = c.request(method, path)
        # 403 expected when token is missing
        enforced += 1 if r.status_code == 403 else 0

    # All protected endpoints must be enforced
    assert enforced == len(protected)
