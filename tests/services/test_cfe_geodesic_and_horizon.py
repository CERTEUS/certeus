#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_geodesic_and_horizon.py     |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_geodesic_and_horizon.py     |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: CFE v0.1 — geodesic/horizon: nagłówki PCO i pola odpowiedzi.

EN: CFE v0.1 — geodesic/horizon: PCO headers and response fields.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_geodesic_and_horizon_headers_present() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r1 = c.post("/v1/cfe/geodesic", json={"case": "LEX-TEST", "facts": {}, "norms": {}})
    assert r1.status_code == 200
    assert "X-CERTEUS-PCO-cfe.geodesic_action" in r1.headers
    body1 = r1.json()
    assert isinstance(body1.get("path"), list) and isinstance(body1.get("geodesic_action"), int | float)

    r2 = c.post("/v1/cfe/horizon", json={"case": "LEX-TEST", "lock": True})
    assert r2.status_code == 200
    assert "X-CERTEUS-PCO-cfe.horizon_mass" in r2.headers
    assert "X-CERTEUS-CFE-Locked" in r2.headers
    body2 = r2.json()
    assert isinstance(body2.get("locked"), bool) and isinstance(body2.get("horizon_mass"), int | float)


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
