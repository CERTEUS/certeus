#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_billing_policies.py              |
# | ROLE: Billing policies endpoints tests                      |
# | PLIK: tests/services/test_billing_policies.py              |
# | ROLA: Testy endpointów polityk billing (tiers/tenant tier)  |
# +-------------------------------------------------------------+
"""
PL: Testy odczytu polityk (tiers/tenants) oraz detekcji tier-u tenant-a.
EN: Tests for reading billing policies and resolving tenant tier.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_policies_and_tenant_tier_endpoints() -> None:
    c = TestClient(app)

    rp = c.get("/v1/billing/policies")
    assert rp.status_code == 200
    pol = rp.json()
    assert isinstance(pol, dict)
    assert "tiers" in pol and isinstance(pol["tiers"], dict)
    assert "free" in pol["tiers"], "default tier 'free' must exist"

    rt = c.get("/v1/billing/tenant_tier", headers={"X-Tenant-ID": "anonymous"})
    assert rt.status_code == 200
    body = rt.json()
    assert body.get("tenant") == "anonymous"
    assert body.get("tier") in {"free", "pro", "enterprise"}
