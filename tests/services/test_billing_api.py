#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_billing_api.py                    |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_billing_api.py                    |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy API billing: quota/allocate/refund i status PENDING → ALLOCATED.
EN: Billing API tests: quota/allocate/refund and PENDING → ALLOCATED flow.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient


def test_billing_quota_allocate_refund_flow() -> None:
    from services.api_gateway.limits import set_tenant_quota
    from services.api_gateway.main import app

    c = TestClient(app)
    tenant = "t-cost"
    set_tenant_quota(tenant, 2)

    # get quota
    r = c.get("/v1/billing/quota", headers={"X-Tenant-ID": tenant})
    assert r.status_code == 200 and int(r.json().get("balance", -1)) == 2

    # allocate 1 -> ALLOCATED, balance 1
    r2 = c.post(
        "/v1/billing/allocate", json={"cost_units": 1}, headers={"X-Tenant-ID": tenant}
    )
    assert r2.status_code == 200 and r2.json().get("status") == "ALLOCATED"

    # allocate 2 (exceeds) -> PENDING, balance unchanged (1)
    r3 = c.post(
        "/v1/billing/allocate", json={"cost_units": 2}, headers={"X-Tenant-ID": tenant}
    )
    assert r3.status_code == 200 and r3.json().get("status") == "PENDING"

    # refund 1 -> balance increases
    r4 = c.post(
        "/v1/billing/refund", json={"units": 1}, headers={"X-Tenant-ID": tenant}
    )
    assert r4.status_code == 200 and int(r4.json().get("balance", -1)) >= 1
