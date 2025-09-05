#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_horizon_domains.py           |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_horizon_domains.py           |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy heurystyki domenowej dla /v1/cfe/horizon (domain + severity).

EN: Domain-aware heuristics tests for /v1/cfe/horizon (domain + severity).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient


def test_horizon_default_no_lock() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post("/v1/cfe/horizon", json={"case": "LEX-CASE-1"})
    assert r.status_code == 200
    js = r.json()
    # No explicit lock, no 'sample' marker
    assert js.get("locked") is False


def test_horizon_med_critical_locks_and_sets_headers() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post(
        "/v1/cfe/horizon",
        json={"case": "MED-CASE-CRIT-1", "domain": "MED", "severity": "critical"},
    )
    assert r.status_code == 200
    js = r.json()
    assert js.get("locked") is True
    assert r.headers.get("X-CERTEUS-PCO-cfe.horizon_mass") is not None
    assert r.headers.get("X-CERTEUS-CFE-Locked") == "true"


def test_horizon_fin_low_no_lock() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post(
        "/v1/cfe/horizon",
        json={"case": "FIN-CASE-LOW-1", "domain": "fin", "severity": "low"},
    )
    assert r.status_code == 200
    assert r.json().get("locked") is False


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
