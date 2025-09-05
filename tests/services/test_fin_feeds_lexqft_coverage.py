#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_fin_feeds_lexqft_coverage.py     |
# | ROLE: FIN→LexQFT coverage feed tests                       |
# | PLIK: tests/services/test_fin_feeds_lexqft_coverage.py     |
# | ROLA: Testy zasilania coverage LexQFT przez FIN measure    |
# +-------------------------------------------------------------+

"""
PL: FIN `/v1/fin/alpha/measure` powinien zasilać agregator LexQFT coverage
    poprzez wewnętrzny append. Sprawdzamy gamma oraz uncaptured.
EN: FIN `/v1/fin/alpha/measure` should feed LexQFT coverage aggregator via
    internal append. Verify gamma and uncaptured.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_fin_measure_updates_lexqft_coverage_state() -> None:
    # Reset coverage to have a clean state
    client.post("/v1/lexqft/coverage/reset")

    # Choose signals to produce predictable p
    # score = sent - risk = 0.8 - 0.2 = 0.6 => p = 0.5 + 0.6/10 = 0.56
    signals = {"risk": 0.2, "sent": 0.8}
    r = client.post("/v1/fin/alpha/measure", json={"signals": signals})
    assert r.status_code == 200

    # Mapping in router: gamma = 0.85 + 0.1*p, unc = 0.2*(1-p)
    p = 0.56
    exp_gamma = 0.85 + 0.1 * p
    exp_unc = 0.2 * (1.0 - p)

    rs = client.get("/v1/lexqft/coverage/state")
    assert rs.status_code == 200
    body = rs.json()
    assert abs(float(body["coverage_gamma"]) - exp_gamma) < 0.02
    assert abs(float(body["uncaptured_mass"]) - exp_unc) < 0.02
