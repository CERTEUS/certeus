#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_fin_tokens.py                   |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_fin_tokens.py                   |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy API Billing/Cost‑Tokens: request → allocate.
EN: Billing/Cost‑Tokens API tests: request → allocate.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path

from fastapi.testclient import TestClient


def test_fin_tokens_request_allocate(tmp_path: Path, monkeypatch) -> None:
    from services.api_gateway.main import app

    # Redirect state file to temp dir to keep tests isolated
    state = tmp_path / "fin_tokens.json"
    monkeypatch.setenv("CERTEUS_TEST_STATE_PATH", str(state))

    # Force reload billing router to pick up env override if used
    import importlib

    import services.api_gateway.routers.billing as billing

    importlib.reload(billing)

    c = TestClient(app)

    r1 = c.post(
        "/v1/fin/tokens/request",
        json={"user_id": "u123", "amount": 50, "purpose": "compute"},
    )
    assert r1.status_code == 200
    req_id = r1.json()["request_id"]
    assert r1.json()["status"] == "PENDING"

    r2 = c.get(f"/v1/fin/tokens/{req_id}")
    assert r2.status_code == 200 and r2.json()["status"] == "PENDING"

    r3 = c.post("/v1/fin/tokens/allocate", json={"request_id": req_id, "allocated_by": "ops"})
    assert r3.status_code == 200 and r3.json()["status"] == "ALLOCATED"

    r4 = c.get(f"/v1/fin/tokens/{req_id}")
    assert r4.status_code == 200 and r4.json()["status"] == "ALLOCATED"
