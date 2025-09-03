#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_billing_admin.py                 |
# | ROLE: Billing admin endpoints tests                         |
# | PLIK: tests/services/test_billing_admin.py                 |
# | ROLA: Testy endpointów admin (set_tier, reload)             |
# +-------------------------------------------------------------+
"""
PL: Testy admin billing — ustawienie tieru i reload z pliku (DEV-guard).
EN: Billing admin tests — set tier and reload from file (DEV-guard).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
from tempfile import TemporaryDirectory

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_admin_set_tier_and_reload(monkeypatch) -> None:
    c = TestClient(app)

    # Without admin flag should be forbidden
    r_forbidden = c.post("/v1/billing/admin/set_tier", json={"tenant": "demo", "tier": "pro"})
    assert r_forbidden.status_code == 403

    with TemporaryDirectory() as td:
        pol_path = Path(td) / "pol.json"
        pol_path.write_text(
            json.dumps({"tiers": {"free": {"daily_quota": 10}, "pro": {"daily_quota": 100}}, "tenants": {}}),
            encoding="utf-8",
        )

        monkeypatch.setenv("BILLING_ADMIN", "1")
        monkeypatch.setenv("BILLING_POLICY_FILE", str(pol_path))
        monkeypatch.setenv("BILLING_POLICY_FILE_WRITE", "1")

        # Set tier and persist
        r1 = c.post("/v1/billing/admin/set_tier", json={"tenant": "demo", "tier": "pro", "persist": True})
        assert r1.status_code == 200
        j1 = r1.json()
        assert j1.get("tenant") == "demo" and j1.get("tier") == "pro"
        assert j1.get("persisted") is True

        # Confirm via GET /policies
        rpol = c.get("/v1/billing/policies")
        assert rpol.status_code == 200
        tenants = rpol.json().get("tenants") or {}
        assert tenants.get("demo") == "pro"

        # Modify file directly and reload
        doc = json.loads(pol_path.read_text(encoding="utf-8"))
        doc["tenants"]["demo2"] = "free"
        pol_path.write_text(json.dumps(doc, ensure_ascii=False), encoding="utf-8")

        rrel = c.post("/v1/billing/admin/reload")
        assert rrel.status_code == 200

        rpol2 = c.get("/v1/billing/policies")
        assert rpol2.status_code == 200
        tenants2 = rpol2.json().get("tenants") or {}
        assert tenants2.get("demo2") == "free"
