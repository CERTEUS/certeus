#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_wkb.py                   |
# | ROLE: LexQFT WKB tunneling tests                            |
# | PLIK: tests/services/test_lexqft_wkb.py                   |
# | ROLA: Testy tunelowania WKB                                 |
# +-------------------------------------------------------------+
"""
PL: W2 — Tunelowanie (WKB-like):
 - Monotoniczność: większa bariera (w albo V0) zmniejsza p_tunnel.
 - Kontrdowody: wartości ujemne w modelu bariery są klamrowane; E > V0 → wysoka p.

EN: W2 — Tunneling (WKB-like):
 - Monotonicity: increasing barrier (w or V0) reduces p_tunnel.
 - Counter-cases: negative barrier params are clamped; E > V0 → high p.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_wkb_probability_monotonic_by_width_and_height() -> None:
    E = 0.3
    # w=1.0
    r1 = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": E, "barrier_model": {"V0": 1.0, "w": 1.0, "m": 1.0}},
    )
    assert r1.status_code == 200
    p1 = float(r1.json()["p_tunnel"])

    # w=2.0 (większa szerokość -> mniejsze p)
    r2 = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": E, "barrier_model": {"V0": 1.0, "w": 2.0, "m": 1.0}},
    )
    assert r2.status_code == 200
    p2 = float(r2.json()["p_tunnel"])
    assert p2 < p1

    # V0=1.5 (wyższa bariera -> mniejsze p)
    r3 = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": E, "barrier_model": {"V0": 1.5, "w": 1.0, "m": 1.0}},
    )
    assert r3.status_code == 200
    p3 = float(r3.json()["p_tunnel"])
    assert p3 < p1


def test_wkb_clamp_and_energy_above_barrier_yields_high_p() -> None:
    # Parametry ujemne -> klamrowane do 0
    r1 = client.post(
        "/v1/lexqft/tunnel",
        json={
            "evidence_energy": 0.4,
            "barrier_model": {"V0": -1.0, "w": -2.0, "m": -3.0},
        },
    )
    assert r1.status_code == 200
    # Wynik ma być w [0,1] i poprawny
    p = float(r1.json()["p_tunnel"])
    assert 0.0 <= p <= 1.0

    # E > V0 -> wysoka szansa tunelowania, a min_energy_to_cross = V0
    r2 = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": 1.2, "barrier_model": {"V0": 0.7, "w": 1.0, "m": 1.0}},
    )
    assert r2.status_code == 200
    body2 = r2.json()
    assert body2["p_tunnel"] >= 0.9
    assert abs(float(body2["min_energy_to_cross"]) - 0.7) < 1e-9
