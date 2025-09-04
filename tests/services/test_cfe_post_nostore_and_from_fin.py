#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_post_nostore_and_from_fin.py |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_post_nostore_and_from_fin.py |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy nagłówków no-store dla POST CFE oraz lensing/from_fin helpera.
EN: Tests for no-store headers on POST CFE and the lensing/from_fin helper.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_post_no_store_and_lensing_from_fin() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r1 = c.post("/v1/cfe/geodesic", json={"case": "LEX-POST", "facts": {}, "norms": {}})
    assert r1.status_code == 200
    assert r1.headers.get("Cache-Control") == "no-store"

    r2 = c.post("/v1/cfe/horizon", json={"case": "LEX-POST", "lock": True})
    assert r2.status_code == 200
    assert r2.headers.get("Cache-Control") == "no-store"

    rf = c.post(
        "/v1/cfe/lensing/from_fin",
        json={"signals": {"risk": 0.2, "sentiment": 0.6}, "seed": "FIN-POST-1"},
    )
    assert rf.status_code == 200
    body = rf.json()
    lm = body.get("lensing_map", {})
    assert isinstance(lm, dict) and len(lm) >= 2
    crit = body.get("critical_precedents", [])
    assert isinstance(crit, list) and len(crit) >= 1
