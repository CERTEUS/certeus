#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_invariants.py                |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_invariants.py                |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Inwarianty CFE: deterministyczna geodezyjna, granice lensingu,
    oraz przepływ lock/recall/revoke dla sprawy.

EN: CFE invariants: deterministic geodesic, lensing bounds,
    and case lock/recall/revoke flow.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient


def test_geodesic_deterministic_headers_and_body() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    payload = {"case": "CFE-INV-1", "facts": {}, "norms": {}}
    r1 = c.post("/v1/cfe/geodesic", json=payload)
    r2 = c.post("/v1/cfe/geodesic", json=payload)
    assert r1.status_code == 200 and r2.status_code == 200
    h1 = r1.headers.get("X-CERTEUS-PCO-cfe.geodesic_action")
    h2 = r2.headers.get("X-CERTEUS-PCO-cfe.geodesic_action")
    assert h1 and h1 == h2
    assert r1.json().get("geodesic_action") == r2.json().get("geodesic_action")


def test_lensing_map_bounds_and_keys() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.get("/v1/cfe/lensing")
    assert r.status_code == 200
    js = r.json()
    lm = js.get("lensing_map", {})
    assert "precedent:K_2001" in lm
    vals = [float(v) for v in lm.values()]
    assert all(0.0 <= v <= 1.0 for v in vals)


def test_case_lock_recall_revoke_flow() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    case = "CFE-INV-LOCK"
    r1 = c.post("/v1/cfe/case/lock", json={"case": case})
    assert r1.status_code == 200 and r1.json().get("locked") is True
    r2 = c.post("/v1/cfe/case/recall", json={"case": case})
    assert r2.status_code == 200 and r2.json().get("locked") is True
    r3 = c.post("/v1/cfe/case/revoke", json={"case": case})
    assert r3.status_code == 200 and r3.json().get("locked") is False


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
