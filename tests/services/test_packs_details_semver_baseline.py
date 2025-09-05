#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_packs_details_semver_baseline.py |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_packs_details_semver_baseline.py |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy GET /v1/packs/{name} — semver_ok i baseline_present dla packów A7.
EN: Tests for GET /v1/packs/{name} — semver_ok and baseline_present for A7 packs.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_packs_details_semver_and_baseline_present_for_a7_packs() -> None:
    c = TestClient(app)
    r = c.get("/v1/packs/")
    assert r.status_code == 200
    names = {i["name"] for i in r.json()}
    for name in ["packs_med", "packs_sec", "packs_code"]:
        assert name in names, f"missing pack {name} in listing"
        d = c.get(f"/v1/packs/{name}")
        assert d.status_code == 200
        body = d.json()
        assert body.get("status", {}).get("semver_ok") is True
        assert body.get("status", {}).get("baseline_present") is True


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
