#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_wkb_properties.py        |
# | ROLE: Property tests for WKB tunneling                      |
# | PLIK: tests/services/test_lexqft_wkb_properties.py        |
# | ROLA: Testy własnościowe tunelowania WKB                    |
# +-------------------------------------------------------------+
"""
PL: Agresywne testy własności WKB:
 - Monotoniczność po szerokości `w` (większe w -> mniejsze p) i wysokości `V0`.
 - Granice: E>=V0 -> p≈0.95; bardzo duże bariery -> p>=floor (0.0005).

EN: Aggressive property tests for WKB tunneling.
"""

from __future__ import annotations

from fastapi.testclient import TestClient
from hypothesis import given, settings, strategies as st

from services.api_gateway.main import app

client = TestClient(app)


@given(
    E=st.floats(min_value=0.0, max_value=2.0, allow_nan=False, allow_infinity=False),
    V0=st.floats(min_value=0.2, max_value=2.0, allow_nan=False, allow_infinity=False),
    w1=st.floats(min_value=0.1, max_value=3.0, allow_nan=False, allow_infinity=False),
    w2=st.floats(min_value=3.1, max_value=6.0, allow_nan=False, allow_infinity=False),
)
@settings(deadline=None, max_examples=60)
def test_wkb_probability_monotonic_width(E: float, V0: float, w1: float, w2: float) -> None:
    # compare p for same E,V0 but different widths
    b = {"V0": float(V0), "w": float(w1), "m": 1.0}
    r1 = client.post("/v1/lexqft/tunnel", json={"evidence_energy": float(E), "barrier_model": b})
    assert r1.status_code == 200
    p1 = float(r1.json()["p_tunnel"]) if V0 > E else 0.95

    b["w"] = float(w2)
    r2 = client.post("/v1/lexqft/tunnel", json={"evidence_energy": float(E), "barrier_model": b})
    assert r2.status_code == 200
    p2 = float(r2.json()["p_tunnel"]) if V0 > E else 0.95

    assert p2 <= p1 + 1e-12


@given(
    E=st.floats(min_value=0.0, max_value=1.5, allow_nan=False, allow_infinity=False),
    V01=st.floats(min_value=0.2, max_value=0.8, allow_nan=False, allow_infinity=False),
    V02=st.floats(min_value=0.9, max_value=2.0, allow_nan=False, allow_infinity=False),
)
@settings(deadline=None, max_examples=60)
def test_wkb_probability_monotonic_height(E: float, V01: float, V02: float) -> None:
    # fixed width,mass
    b1 = {"V0": float(V01), "w": 1.5, "m": 1.0}
    b2 = {"V0": float(V02), "w": 1.5, "m": 1.0}

    r1 = client.post("/v1/lexqft/tunnel", json={"evidence_energy": float(E), "barrier_model": b1})
    assert r1.status_code == 200
    p1 = float(r1.json()["p_tunnel"]) if V01 > E else 0.95

    r2 = client.post("/v1/lexqft/tunnel", json={"evidence_energy": float(E), "barrier_model": b2})
    assert r2.status_code == 200
    p2 = float(r2.json()["p_tunnel"]) if V02 > E else 0.95

    assert p2 <= p1 + 1e-12


def test_wkb_extremes_floor_and_cross() -> None:
    # Cross barrier: E>=V0 → p≈0.95
    r = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": 1.1, "barrier_model": {"V0": 1.0, "w": 5.0, "m": 1.0}},
    )
    assert r.status_code == 200 and float(r.json()["p_tunnel"]) >= 0.9

    # Very large barrier should not go below floor (0.0005)
    r2 = client.post(
        "/v1/lexqft/tunnel",
        json={
            "evidence_energy": 0.0,
            "barrier_model": {"V0": 5.0, "w": 50.0, "m": 10.0},
        },
    )
    assert r2.status_code == 200 and float(r2.json()["p_tunnel"]) >= 0.0005
