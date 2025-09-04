#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_boundary_endpoint.py            |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_boundary_endpoint.py            |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Smoke dla Boundary: /v1/boundary/status oraz /v1/boundary/reconstruct

EN: Boundary smoke: /v1/boundary/status and /v1/boundary/reconstruct
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_boundary_status_and_reconstruct_smoke(tmp_path) -> None:
    # Ensure empty bundle dir for deterministic zeros
    import os

    os.environ["PROOF_BUNDLE_DIR"] = str(tmp_path)

    from services.api_gateway.main import app

    c = TestClient(app)

    r1 = c.get("/v1/boundary/status")
    assert r1.status_code == 200
    body1 = r1.json()
    assert isinstance(body1.get("delta_bits"), int)
    assert isinstance(body1.get("bits_delta_map"), dict)

    r2 = c.post("/v1/boundary/reconstruct")
    assert r2.status_code == 200
    body2 = r2.json()
    assert "bits_delta_map" in body2 and "stats" in body2


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
