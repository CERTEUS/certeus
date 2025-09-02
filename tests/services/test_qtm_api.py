#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_qtm_api.py                       |
# | ROLE: QTMP API tests: init_case, measure, commutator, deco |
# | PLIK: tests/services/test_qtm_api.py                       |
# | ROLA: Testy API QTMP: init_case, measure, commutator, deco |
# +-------------------------------------------------------------+

"""
PL: Testy podstawowych endpointów QTMP (pomiar, presety, komutatory, dekoherencja).
EN: Tests for core QTMP endpoints (measurement, presets, commutator, decoherence).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === KONFIGURACJA / CONFIGURATION ===

client = TestClient(app)

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def test_qtm_init_case_uniform_predistribution() -> None:
    r = client.post(
        "/v1/qtm/init_case",
        json={"case": "LEX-QTMP-1", "basis": ["ALLOW", "DENY", "ABSTAIN"], "state_uri": "psi://uniform"},
    )
    assert r.status_code == 200
    body = r.json()
    predis = body["predistribution"]
    assert len(predis) == 3
    probs = [float(x["p"]) for x in predis]
    # Uniform-ish and normalized
    assert all(0.0 < p <= 1.0 for p in probs)
    assert round(sum(probs), 6) in (1.0, 0.999999, 1.000001)


def test_qtm_measure_headers_and_fields() -> None:
    # set decoherence for this case
    client.post("/v1/qtm/decoherence", json={"case": "ui", "channel": "dephasing", "gamma": 0.1})

    r = client.post("/v1/qtm/measure", json={"operator": "L", "source": "ui"})
    assert r.status_code == 200
    body = r.json()
    assert set(body.keys()) >= {"verdict", "p", "collapse_log", "uncertainty_bound", "latency_ms"}
    # Headers with PCO snippets should be present
    hdrs = r.headers
    assert "X-CERTEUS-PCO-qtm.collapse_event" in hdrs
    assert "X-CERTEUS-PCO-qtmp.priorities" in hdrs


def test_qtm_measure_uses_preset_operator_if_available() -> None:
    case_id = "LEX-QTMP-PRESET-FALLBACK"
    client.post("/v1/qtm/preset", json={"case": case_id, "operator": "T"})
    r = client.post("/v1/qtm/measure", json={"operator": "W", "source": "ui", "case": case_id})
    assert r.status_code == 200
    hdr = r.headers.get("X-CERTEUS-PCO-qtm.collapse_event", "{}")
    # very small parser to avoid json import; string contains operator":"T"
    assert '\"operator\":\"T\"' in hdr


def test_qtm_state_endpoint_after_init() -> None:
    case_id = "LEX-QTMP-STATE-1"
    client.post("/v1/qtm/init_case", json={"case": case_id, "basis": ["ALLOW", "DENY"]})
    r = client.get(f"/v1/qtm/state/{case_id}")
    assert r.status_code == 200
    body = r.json()
    assert body["case"] == case_id and body["basis"] == ["ALLOW", "DENY"]


def test_qtm_commutator_simple_rule() -> None:
    r_eq = client.post("/v1/qtm/commutator", json={"A": "L", "B": "L"})
    r_ne = client.post("/v1/qtm/commutator", json={"A": "L", "B": "T"})
    assert r_eq.status_code == 200 and r_ne.status_code == 200
    assert r_eq.json()["value"] == 0.0
    assert r_ne.json()["value"] == 1.0


def test_qtm_find_entanglement_pairs() -> None:
    r = client.post("/v1/qtm/find_entanglement", json={"variables": ["a", "b", "c", "d", "e"]})
    assert r.status_code == 200
    body = r.json()
    assert body["pairs"] == [["a", "b"], ["c", "d"]]
    assert 0.0 <= body["mi"] <= 1.0
    assert 0.0 <= body["negativity"] <= 1.0


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
