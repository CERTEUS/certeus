#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_billing_api.py                   |
# | ROLE: Project test.                                         |
# | PLIK: tests/services/test_billing_api.py                   |
# | ROLA: Testy API Billing (quota/balance/refund/allocate).    |
# +-------------------------------------------------------------+

"""
PL: Testy Billing – ustawianie limitu, saldo, refund i alokacja.

EN: Billing tests – set quota, balance, refund and allocation.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_quota_balance_allocate_refund_roundtrip():
    c = TestClient(app)

    # Ustaw quota dla TENANT-X
    r1 = c.post("/v1/billing/quota", json={"tenant": "TENANT-X", "units": 50})
    assert r1.status_code == 200
    assert r1.json().get("balance") == 50

    # Balance z nagłówkiem tenant-a (X-Tenant-ID)
    r2 = c.get("/v1/billing/balance", headers={"X-Tenant-ID": "TENANT-X"})
    assert r2.status_code == 200
    assert r2.json().get("balance") == 50

    # Allocate +20
    r3 = c.post(
        "/v1/billing/allocate",
        json={"units": 20},
        headers={"X-Tenant-ID": "TENANT-X"},
    )
    assert r3.status_code == 200
    assert r3.json().get("balance") == 70

    # Refund +5 (po nazwie tenant-a)
    r4 = c.post("/v1/billing/refund", json={"tenant": "TENANT-X", "units": 5})
    assert r4.status_code == 200
    assert r4.json().get("balance") == 75
