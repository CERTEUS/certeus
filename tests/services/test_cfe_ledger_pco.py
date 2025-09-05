#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_ledger_pco.py                |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_ledger_pco.py                |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy CFE: PCO nagłówki + zapis do Ledger dla geodesic/horizon.
EN: CFE tests: PCO headers + Ledger record for geodesic/horizon.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

def test_geodesic_sets_pco_and_writes_ledger() -> None:
    from services.api_gateway.main import app
    from services.ledger_service.ledger import ledger_service

    c = TestClient(app)
    case = "CFE-LEDGER-1"
    before = len(ledger_service.get_records_for_case(case_id=case))
    r = c.post("/v1/cfe/geodesic", json={"case": case, "facts": {}, "norms": {}})
    assert r.status_code == 200
    assert r.headers.get("X-CERTEUS-PCO-cfe.geodesic_action") is not None
    after = len(ledger_service.get_records_for_case(case_id=case))
    assert after == before + 1

def test_horizon_sets_pco_and_writes_ledger() -> None:
    from services.api_gateway.main import app
    from services.ledger_service.ledger import ledger_service

    c = TestClient(app)
    case = "CFE-LEDGER-2"
    before = len(ledger_service.get_records_for_case(case_id=case))
    r = c.post("/v1/cfe/horizon", json={"case": case, "lock": True})
    assert r.status_code == 200
    assert r.headers.get("X-CERTEUS-PCO-cfe.horizon_mass") is not None
    after = len(ledger_service.get_records_for_case(case_id=case))
    assert after == before + 1

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
