#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/api/test_openapi_docs_json.py                  |
# | ROLE: Docs OpenAPI JSON endpoint test                       |
# | PLIK: tests/api/test_openapi_docs_json.py                  |
# | ROLA: Test /v1/openapi/docs                                  |
# +-------------------------------------------------------------+
"""
PL: Sprawdza, czy /v1/openapi/docs zwraca słownik z kluczami openapi/paths.
EN: Verifies that /v1/openapi/docs returns a dict with openapi/paths keys.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_openapi_docs_json_endpoint() -> None:
    c = TestClient(app)
    r = c.get("/v1/openapi/docs")
    assert r.status_code == 200
    j = r.json()
    assert isinstance(j, dict)
    assert "paths" in j
    assert "openapi" in j
