#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_coverage_contributions.py |
# | ROLE: LexQFT coverage contributions audit tests            |
# | PLIK: tests/services/test_lexqft_coverage_contributions.py |
# | ROLA: Testy listy wkładów coverage LexQFT                  |
# +-------------------------------------------------------------+

"""
PL: Test audytu wkładów coverage: update -> contributions, potem FIN feed -> wzrost.
EN: Audit raw coverage contributions: update -> contributions, then FIN feed -> grows.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_coverage_contributions_list_and_growth_via_fin() -> None:
    client.post("/v1/lexqft/coverage/reset")

    items = [
        {"gamma": 0.9, "weight": 2.0, "uncaptured": 0.05},
        {"gamma": 0.7, "weight": 1.0, "uncaptured": 0.15},
    ]
    r = client.post("/v1/lexqft/coverage/update", json=items)
    assert r.status_code == 200

    rc = client.get("/v1/lexqft/coverage/contributions")
    assert rc.status_code == 200
    arr = rc.json()
    assert isinstance(arr, list) and len(arr) == 2

    # FIN measure adds one more contribution
    signals = {"risk": 0.2, "sent": 0.8}
    rf = client.post("/v1/fin/alpha/measure", json={"signals": signals})
    assert rf.status_code == 200

    rc2 = client.get("/v1/lexqft/coverage/contributions")
    assert rc2.status_code == 200
    arr2 = rc2.json()
    assert len(arr2) == 3
