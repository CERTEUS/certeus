#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_from_fin_properties.py   |
# | ROLE: Property tests for FIN→coverage                       |
# | PLIK: tests/services/test_lexqft_from_fin_properties.py   |
# | ROLA: Testy własnościowe FIN→coverage                        |
# +-------------------------------------------------------------+
"""
PL: Agresywne własności dla FIN→coverage:
 - Gamma w [0.6, 0.98], uncaptured w [0.0, 0.2].
 - Monotoniczność po `score = sent - risk`.
"""

from __future__ import annotations

from fastapi.testclient import TestClient
from hypothesis import given, settings, strategies as st

from services.api_gateway.main import app

client = TestClient(app)


def _from_fin(sent: float, risk: float):
    r = client.post(
        "/v1/lexqft/coverage/from_fin",
        json={
            "signals": {"sentiment": float(sent), "risk": float(risk)},
            "weight": 1.0,
            "uncaptured_base": 0.1,
        },
    )
    assert r.status_code == 200
    body = r.json()
    return float(body["gamma"]), float(body["uncaptured"])


@given(
    sent1=st.floats(
        min_value=-2.0, max_value=2.0, allow_nan=False, allow_infinity=False
    ),
    risk1=st.floats(
        min_value=-2.0, max_value=2.0, allow_nan=False, allow_infinity=False
    ),
    sent2=st.floats(
        min_value=-2.0, max_value=2.0, allow_nan=False, allow_infinity=False
    ),
    risk2=st.floats(
        min_value=-2.0, max_value=2.0, allow_nan=False, allow_infinity=False
    ),
)
@settings(deadline=None, max_examples=60)
def test_fin_coverage_ranges_and_monotonicity(sent1, risk1, sent2, risk2) -> None:
    client.post("/v1/lexqft/coverage/reset")

    g1, u1 = _from_fin(sent1, risk1)
    assert 0.6 <= g1 <= 0.98
    assert 0.0 <= u1 <= 0.2

    g2, u2 = _from_fin(sent2, risk2)
    score1 = float(sent1) - float(risk1)
    score2 = float(sent2) - float(risk2)
    if score2 > score1 + 1e-12:
        assert g2 >= g1 - 1e-9
        assert u2 <= u1 + 1e-9
