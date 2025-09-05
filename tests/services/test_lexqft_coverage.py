#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_coverage.py               |
# | ROLE: LexQFT coverage/state/update tests                    |
# | PLIK: tests/services/test_lexqft_coverage.py               |
# | ROLA: Testy coverage/state/update LexQFT                    |
# +-------------------------------------------------------------+

"""
PL: Testy agregatora pokrycia LexQFT: domyślne /coverage,
    oraz aktualizacja /coverage/update i odczyt /coverage/state.
EN: Tests for LexQFT coverage aggregator: default /coverage,
    and /coverage/update + /coverage/state readback.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_lexqft_coverage_default_and_update_roundtrip() -> None:
    # Reset any previous state
    client.post("/v1/lexqft/coverage/reset")

    r0 = client.get("/v1/lexqft/coverage")
    assert r0.status_code == 200
    # Update coverage with two items (weighted)
    items = [
        {"gamma": 0.9, "weight": 2.0, "uncaptured": 0.05},
        {"gamma": 0.7, "weight": 1.0, "uncaptured": 0.15},
    ]
    ru = client.post("/v1/lexqft/coverage/update", json=items)
    assert ru.status_code == 200 and ru.json().get("count") == 2

    rs = client.get("/v1/lexqft/coverage/state")
    assert rs.status_code == 200
    body = rs.json()
    # weighted gamma: (0.9*2 + 0.7*1)/(2+1) = 2.5/3 ~= 0.833333
    assert 0.83 <= float(body["coverage_gamma"]) <= 0.84
    # weighted uncaptured: (0.05*2 + 0.15*1)/3 = 0.25/3 ~= 0.08333
    assert 0.08 <= float(body["uncaptured_mass"]) <= 0.09
