#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_i18n_negotiation.py              |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_i18n_negotiation.py              |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy negocjacji języka (i18n): Accept-Language / ?lang → Content-Language,
    oraz niezmienność PCO (proof-native) względem języka.

EN: i18n negotiation tests: Accept-Language / ?lang → Content-Language,
    and language-invariant PCO (proof-native) headers.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_content_language_default_and_header_override() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    # Default: no header → pl
    r0 = c.get("/health")
    assert r0.status_code == 200
    assert r0.headers.get("Content-Language") == "pl"
    # Header en → en
    r1 = c.get("/health", headers={"Accept-Language": "en"})
    assert r1.status_code == 200
    assert r1.headers.get("Content-Language") == "en"


def test_lang_query_param_overrides_header() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.get("/health?lang=en", headers={"Accept-Language": "pl"})
    assert r.status_code == 200
    assert r.headers.get("Content-Language") == "en"


def test_pco_headers_stable_across_languages() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    payload = {"operator": "L", "source": "CASE-I18N"}
    r_pl = c.post("/v1/qtm/measure", json=payload, headers={"Accept-Language": "pl"})
    r_en = c.post("/v1/qtm/measure", json=payload, headers={"Accept-Language": "en"})
    assert r_pl.status_code == 200 and r_en.status_code == 200
    h_pl = r_pl.headers.get("X-CERTEUS-PCO-qtm.collapse_event")
    h_en = r_en.headers.get("X-CERTEUS-PCO-qtm.collapse_event")
    assert h_pl and h_en and h_pl == h_en


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
