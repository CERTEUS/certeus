#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_virtual_pairs.py         |
# | ROLE: LexQFT virtual pairs tests                            |
# | PLIK: tests/services/test_lexqft_virtual_pairs.py         |
# | ROLA: Testy wirtualnych par (budżet/energy_debt)            |
# +-------------------------------------------------------------+
"""
PL: W3 — Wirtualne pary:
 - Ustaw budżet energii, spawn w ramach budżetu, stan/remaining zgodne.
 - Próba przekroczenia budżetu daje 409 i nie zmienia stanu.

EN: W3 — Virtual pairs:
 - Set energy budget, spawn within, state/remaining are correct.
 - Over-budget spawn returns 409 and does not change state.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_virtual_pairs_budget_and_spawn_within_budget() -> None:
    # Reset and set budget
    client.post("/v1/lexqft/virtual_pairs/reset")
    r0 = client.post("/v1/lexqft/virtual_pairs/budget", json={"case": "TST-000001", "budget": 10.0})
    assert r0.status_code == 200
    s0 = r0.json()
    assert float(s0["budget"]) == 10.0 and float(s0["energy_debt"]) == 0.0

    # Spawn 3 pairs × 2.0 energy
    r1 = client.post(
        "/v1/lexqft/virtual_pairs/spawn",
        json={"case": "TST-000001", "pairs": 3, "energy_per_pair": 2.0},
    )
    assert r1.status_code == 200
    s1 = r1.json()
    assert int(s1["pairs"]) == 3
    assert abs(float(s1["energy_debt"]) - 6.0) < 1e-9
    assert abs(float(s1["remaining"]) - 4.0) < 1e-9


def test_virtual_pairs_over_budget_is_blocked() -> None:
    # Given remaining 4.0 from previous test, try to spend 5.0
    r = client.post(
        "/v1/lexqft/virtual_pairs/spawn",
        json={"case": "TST-000001", "pairs": 5, "energy_per_pair": 1.0},
    )
    assert r.status_code == 409
    # State unchanged
    s = client.get("/v1/lexqft/virtual_pairs/state", params={"case": "TST-000001"}).json()
    assert int(s["pairs"]) == 3
    assert abs(float(s["energy_debt"]) - 6.0) < 1e-9
    assert abs(float(s["remaining"]) - 4.0) < 1e-9
