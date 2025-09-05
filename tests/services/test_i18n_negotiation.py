#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_i18n_negotiation.py               |
# | ROLE: Project test module.                                  |
# | PLIK: tests/services/test_i18n_negotiation.py               |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Testy i18n: negocjacja nagłówka Content-Language oraz niezmienność PCO
    (proof-native) względem języka dla głównych endpointów.

EN: i18n tests: Content-Language negotiation and proof-native invariance
    across languages for main endpoints.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

def test_i18n_accept_language_header() -> None:
    c = TestClient(app)
    r = c.get("/health", headers={"Accept-Language": "en-US,en;q=0.8"})
    assert r.status_code == 200
    assert r.headers.get("Content-Language") == "en"

def test_i18n_lang_query_param_overrides_header() -> None:
    c = TestClient(app)
    r = c.get("/health?lang=pl", headers={"Accept-Language": "en"})
    assert r.status_code == 200
    assert r.headers.get("Content-Language") == "pl"

def test_pco_qtm_stable_across_languages() -> None:
    c = TestClient(app)
    payload = {"operator": "L", "source": "CASE-I18N"}
    r_pl = c.post("/v1/qtm/measure?lang=pl", json=payload)
    r_en = c.post("/v1/qtm/measure?lang=en", json=payload)
    assert r_pl.status_code == 200 and r_en.status_code == 200
    h_pl = r_pl.headers.get("X-CERTEUS-PCO-qtm.collapse_event")
    h_en = r_en.headers.get("X-CERTEUS-PCO-qtm.collapse_event")
    assert h_pl and h_en and h_pl == h_en

def test_pco_cfe_and_lexqft_stable_across_languages() -> None:
    c = TestClient(app)
    # CFE geodesic — compare PCO header
    g_pl = c.post("/v1/cfe/geodesic?lang=pl", json={"case": "CASE-I18N"})
    g_en = c.post("/v1/cfe/geodesic?lang=en", json={"case": "CASE-I18N"})
    assert g_pl.status_code == 200 and g_en.status_code == 200
    a_pl = g_pl.headers.get("X-CERTEUS-PCO-cfe.geodesic_action")
    a_en = g_en.headers.get("X-CERTEUS-PCO-cfe.geodesic_action")
    assert a_pl and a_en and a_pl == a_en
    # LexQFT tunnel — compare body content
    t_pl = c.post("/v1/lexqft/tunnel?lang=pl", json={"evidence_energy": 1.0})
    t_en = c.post("/v1/lexqft/tunnel?lang=en", json={"evidence_energy": 1.0})
    assert t_pl.status_code == 200 and t_en.status_code == 200
    assert t_pl.json() == t_en.json()

def test_static_page_has_content_language_header() -> None:
    c = TestClient(app)
    r = c.get("/app/public/marketplace.html?lang=en", headers={"Accept-Language": "pl"})
    assert r.status_code == 200
    assert r.headers.get("Content-Language") == "en"
