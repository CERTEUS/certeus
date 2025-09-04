#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_from_fin.py              |
# | ROLE: LexQFT coverage from FIN tests                        |
# | PLIK: tests/services/test_lexqft_from_fin.py              |
# | ROLA: Testy coverage z danych FIN                           |
# +-------------------------------------------------------------+
"""
PL: W5 — Path-coverage karmione danymi FIN:
 - Przy wysokim sentymencie wobec ryzyka gamma >= 0.9 i uncaptured <= 0.05.
 - Przy wyższym ryzyku gamma spada, uncaptured rośnie.
EN: FIN-driven coverage:
 - High sentiment vs risk -> gamma >= 0.9, uncaptured <= 0.05.
 - Higher risk -> lower gamma, higher uncaptured.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_coverage_from_fin_high_sentiment_low_risk() -> None:
    client.post("/v1/lexqft/coverage/reset")
    r = client.post(
        "/v1/lexqft/coverage/from_fin",
        json={"signals": {"sentiment": 0.8, "risk": 0.1}, "weight": 2.0, "uncaptured_base": 0.08},
    )
    assert r.status_code == 200
    body = r.json()
    assert float(body["gamma"]) >= 0.9
    assert float(body["uncaptured"]) <= 0.05
    s = client.get("/v1/lexqft/coverage/state").json()
    assert float(s["coverage_gamma"]) >= 0.9
    assert float(s["uncaptured_mass"]) <= 0.05


def test_coverage_from_fin_high_risk_low_sentiment() -> None:
    client.post("/v1/lexqft/coverage/reset")
    r = client.post(
        "/v1/lexqft/coverage/from_fin",
        json={"signals": {"sent": 0.1, "risk_factor": 0.9}, "weight": 1.0, "uncaptured_base": 0.1},
    )
    assert r.status_code == 200
    body = r.json()
    assert float(body["gamma"]) <= 0.85
    assert float(body["uncaptured"]) >= 0.08
