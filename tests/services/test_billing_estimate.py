#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_billing_estimate.py              |
# | ROLE: Billing estimate endpoint test                        |
# | PLIK: tests/services/test_billing_estimate.py              |
# | ROLA: Test endpointu /v1/billing/estimate                   |
# +-------------------------------------------------------------+
"""
PL: Prosty test szacowania kosztu akcji (qtm.measure).
EN: Simple test for action cost estimation (qtm.measure).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_estimate_qtm_measure() -> None:
    c = TestClient(app)
    r = c.post("/v1/billing/estimate", json={"action": "qtm.measure"}, headers={"X-Tenant-ID": "acme"})
    assert r.status_code == 200
    out = r.json()
    assert out.get("tenant") == "acme"
    assert out.get("action") == "qtm.measure"
    assert isinstance(out.get("estimated_units"), int)
    assert out.get("estimated_units", 0) >= 1
