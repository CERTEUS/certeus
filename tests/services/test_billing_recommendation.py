#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_billing_recommendation.py        |
# | ROLE: Billing recommendation endpoint test                  |
# | PLIK: tests/services/test_billing_recommendation.py        |
# | ROLA: Test rekomendacji tieru na podstawie akcji i wolumenu |
# +-------------------------------------------------------------+
"""
PL: Test rekomendacji tieru: dla dużego wolumenu nie powinno proponować 'free'.
EN: Recommendation test: for large volume it should not propose 'free'.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_billing_recommendation() -> None:
    c = TestClient(app)
    r = c.get("/v1/billing/recommendation", params={"action": "qtm.measure", "monthly": 100000, "days": 30})
    assert r.status_code == 200
    j = r.json()
    assert j.get("action") == "qtm.measure"
    assert j.get("recommended_tier") in {"pro", "enterprise", "free"}
    # For very high volume, free likely insufficient
    if j.get("tiers"):
        assert j.get("recommended_tier") != "free"
