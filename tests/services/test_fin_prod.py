#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_fin_prod.py                      |
# | ROLE: FIN production hardening tests                          |
# | PLIK: tests/services/test_fin_prod.py                      |
# | ROLA: Testy produkcyjne FIN (polityki, PnL)                   |
# +-------------------------------------------------------------+

"""
PL: W11 — polityka ryzyka w measure oraz PnL agregacja dwóch strategii.

EN: W11 — risk policy in measure and PnL aggregation of two strategies.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json

from fastapi.testclient import TestClient


def test_fin_measure_policy_violation_header() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    # High risk to trigger violation
    r = c.post("/v1/fin/alpha/measure", json={"signals": {"risk": 0.95, "sentiment": 0.1}})
    assert r.status_code == 200
    hdr = r.headers.get("X-CERTEUS-Policy-FIN")
    assert isinstance(hdr, str) and hdr
    pol = json.loads(hdr)
    assert pol.get("policy_ok") is False and "risk_above_max" in pol.get("violations", [])


def test_fin_simulate_two_strategies_and_pnl() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    # two runs
    c.post(
        "/v1/fin/alpha/simulate",
        json={"strategy_id": "qalpha-momentum", "capital": 1000, "horizon_days": 5},
    )
    c.post(
        "/v1/fin/alpha/simulate",
        json={"strategy_id": "qalpha-arb", "capital": 1000, "horizon_days": 5},
    )
    r = c.get("/v1/fin/alpha/pnl")
    assert r.status_code == 200
    runs = r.json().get("runs")
    assert isinstance(runs, list) and len(runs) >= 2
