#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_qtm_pco_headers.py               |
# | ROLE: QTMP PCO headers contract tests                      |
# | PLIK: tests/services/test_qtm_pco_headers.py               |
# | ROLA: Testy kontraktu nagłówków PCO dla QTMP               |
# +-------------------------------------------------------------+

"""
PL: Testy weryfikujące obecność i podstawową poprawność nagłówków PCO
    zwracanych przez `/v1/qtm/measure`.

EN: Tests verifying presence and basic correctness of PCO headers
    returned by `/v1/qtm/measure`.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json

from fastapi.testclient import TestClient


def test_qtm_measure_emits_pco_headers() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    case = "HDR-QTMP-1"
    # Ensure predistribution exists for predistribution header
    r0 = c.post("/v1/qtm/init_case", json={"case": case, "basis": ["ALLOW", "DENY", "ABSTAIN"]})
    assert r0.status_code == 200

    r = c.post("/v1/qtm/measure", json={"operator": "L", "source": "ui", "case": case})
    assert r.status_code == 200
    h = r.headers
    # Required PCO headers
    assert "X-CERTEUS-PCO-qtm.collapse_event" in h
    assert "X-CERTEUS-PCO-qtmp.priorities" in h
    # Optional but expected with init_case
    assert "X-CERTEUS-PCO-qtm.predistribution[]" in h
    assert "X-CERTEUS-PCO-qtm.collapse_prob" in h
    assert "X-CERTEUS-PCO-qtm.collapse_latency_ms" in h
    assert "X-CERTEUS-PCO-correlation.cfe_qtmp" in h

    # Sanity parse
    pred = json.loads(h.get("X-CERTEUS-PCO-qtm.predistribution[]", "[]"))
    assert isinstance(pred, list) and len(pred) == 3
    p = float(h.get("X-CERTEUS-PCO-qtm.collapse_prob", "0"))
    assert 0.0 <= p <= 1.0
    lat = float(h.get("X-CERTEUS-PCO-qtm.collapse_latency_ms", "0"))
    assert lat >= 0.0
