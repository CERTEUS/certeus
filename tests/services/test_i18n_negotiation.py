#!/usr/bin/env python3

"""
PL: Test i18n negocjacji języka — nagłówek `Accept-Language` i parametr `lang`
    powinny sterować nagłówkiem `Content-Language`.

EN: i18n negotiation test — `Accept-Language` and `lang` parameter should
    control the `Content-Language` response header.
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
