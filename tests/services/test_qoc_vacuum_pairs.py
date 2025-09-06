#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_qoc_vacuum_pairs.py              |
# | ROLE: QOC vacuum_pairs/energy_debt tests                   |
# | PLIK: tests/services/test_qoc_vacuum_pairs.py              |
# | ROLA: Testy QOC: vacuum_pairs i energy_debt                |
# +-------------------------------------------------------------+

"""
PL: Testy endpointów QOC (pary próżni): vacuum_pairs (PCO) i energy_debt.
EN: Tests for QOC endpoints: vacuum_pairs (PCO headers) and energy_debt.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_qoc_vacuum_pairs_emits_pco_and_reasonable_rate() -> None:
    r = client.post(
        "/v1/qoc/vacuum_pairs", json={"vacuum_energy": 2.0, "horizon_scale": 1.2}
    )
    assert r.status_code == 200
    body = r.json()
    assert 0.05 <= float(body["rate"]) <= 1.0
    assert body["pairs_count"] >= 0
    # PCO headers present
    assert "X-CERTEUS-PCO-qoc.vacuum_pairs.rate" in r.headers


def test_qoc_energy_debt_simple_product() -> None:
    r = client.post("/v1/qoc/energy_debt", json={"pairs_count": 5, "mean_energy": 1.25})
    assert r.status_code == 200
    body = r.json()
    assert abs(float(body["energy_debt"]) - 6.25) < 1e-6
