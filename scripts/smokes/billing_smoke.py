#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/billing_smoke.py                      |
# | ROLE: Project script.                                        |
# | PLIK: scripts/smokes/billing_smoke.py                      |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Lekki smoke Billing (quota/balance/allocate/refund) via TestClient -> JSON report.
EN: Lightweight Billing smoke (quota/balance/allocate/refund) via TestClient -> JSON report.
"""

from __future__ import annotations

import json
from pathlib import Path

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def main() -> int:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    out = {}
    with TestClient(app) as c:
        t = "smoke-tenant"
        out["quota"] = c.post("/v1/billing/quota", json={"tenant": t, "units": 10}).json()
        out["bal0"] = c.get("/v1/billing/balance", headers={"X-Tenant-ID": t}).json()
        out["alloc"] = c.post("/v1/billing/allocate", json={"units": 3}, headers={"X-Tenant-ID": t}).json()
        out["refund"] = c.post("/v1/billing/refund", json={"tenant": t, "units": 2}).json()
        out["bal1"] = c.get("/v1/billing/balance", headers={"X-Tenant-ID": t}).json()
    (reports / "smoke_billing.json").write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
    print("smoke_billing -> reports/smoke_billing.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
