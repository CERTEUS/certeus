#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_rtbf_endpoints.py               |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_rtbf_endpoints.py               |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Smoke testy RTBF endpointów ProofGate: appeal/erase/erased.
EN: Smoke tests for ProofGate RTBF endpoints: appeal/erase/erased.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.proofgate.app import app


def test_rtbf_endpoints_smoke() -> None:
    c = TestClient(app)
    case = "CER-LEX-RTBF-TST"
    r1 = c.post("/v1/rtbf/appeal", json={"case_id": case, "reason": "user_request"})
    assert r1.status_code == 200
    assert r1.json().get("status") == "RECEIVED"

    r2 = c.post("/v1/rtbf/erase", json={"case_id": case})
    assert r2.status_code == 200
    assert r2.json().get("status") == "ERASED"

    r3 = c.get(f"/v1/rtbf/erased/{case}")
    assert r3.status_code == 200
    assert r3.json().get("erased") is True


# === TESTY / TESTS ===
