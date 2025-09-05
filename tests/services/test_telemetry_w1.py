#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_telemetry_w1.py                  |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_telemetry_w1.py                  |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Telemetria bazowa (W1 D4): /v1/cfe/curvature i /v1/lexqft/coverage.

EN: Base telemetry (W1 D4): /v1/cfe/curvature and /v1/lexqft/coverage.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_cfe_curvature_and_lexqft_coverage_endpoints() -> None:
    from services.api_gateway.main import app

    client = TestClient(app)

    r1 = client.get("/v1/cfe/curvature")
    assert r1.status_code == 200
    body1 = r1.json()
    assert isinstance(body1.get("kappa_max"), int | float)

    r2 = client.get("/v1/lexqft/coverage")
    assert r2.status_code == 200
    body2 = r2.json()
    assert 0.0 <= float(body2.get("coverage_gamma", 0)) <= 1.0


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
