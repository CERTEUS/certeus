#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/tenant_isolation_check.py           |
# | ROLE: SLO/Isolation gate (report-only)                       |
# | PLIK: scripts/slo_gate/tenant_isolation_check.py           |
# | ROLA: Bramka SLO/izolacji (raport)                           |
# +-------------------------------------------------------------+

"""
PL: Sprawdza izolację per-tenant dla Billing API: operacje na TENANT-A nie
    wpływają na balans TENANT-B i odwrotnie. Report‑only (exit 0); sygnalizuje
    wynik w stdout.

EN: Checks per-tenant isolation for Billing API: operations on TENANT-A do not
    affect TENANT-B and vice versa. Report‑only (exit 0); prints status.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===

from fastapi.testclient import TestClient

from services.api_gateway.limits import set_tenant_quota
from services.api_gateway.main import app

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

def main() -> int:  # pragma: no cover (integration)
    c = TestClient(app)
    a, b = "tenant-A", "tenant-B"
    set_tenant_quota(a, 2)
    set_tenant_quota(b, 2)

    r_a0 = c.get("/v1/billing/quota", headers={"X-Tenant-ID": a}).json()
    r_b0 = c.get("/v1/billing/quota", headers={"X-Tenant-ID": b}).json()
    ok = int(r_a0.get("balance", -1)) == 2 and int(r_b0.get("balance", -1)) == 2

    c.post("/v1/billing/allocate", json={"cost_units": 1}, headers={"X-Tenant-ID": a})
    r_a1 = c.get("/v1/billing/quota", headers={"X-Tenant-ID": a}).json()
    r_b1 = c.get("/v1/billing/quota", headers={"X-Tenant-ID": b}).json()
    ok = ok and int(r_a1.get("balance", -1)) == 1 and int(r_b1.get("balance", -1)) == 2

    c.post("/v1/billing/allocate", json={"cost_units": 1}, headers={"X-Tenant-ID": b})
    r_a2 = c.get("/v1/billing/quota", headers={"X-Tenant-ID": a}).json()
    r_b2 = c.get("/v1/billing/quota", headers={"X-Tenant-ID": b}).json()
    ok = ok and int(r_a2.get("balance", -1)) == 1 and int(r_b2.get("balance", -1)) == 1

    print(f"Tenant isolation: {'OK' if ok else 'WARN'}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
