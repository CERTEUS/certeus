#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_cache_headers_and_warm.py    |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_cache_headers_and_warm.py    |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy nagłówków cache i endpointu warm cache dla CFE.
EN: Tests for cache headers and warm cache endpoint for CFE.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_cfe_cache_headers_present(monkeypatch) -> None:
    from services.api_gateway.main import app

    monkeypatch.setenv("CFE_CACHE_TTL_SEC", "120")
    c = TestClient(app)
    r1 = c.get("/v1/cfe/curvature?case_id=CACHE-TEST")
    assert r1.status_code == 200
    assert "Cache-Control" in r1.headers
    assert "max-age=120" in r1.headers.get("Cache-Control", "")
    assert r1.headers.get("X-CERTEUS-CFE-Cache-TTL") == "120"

    r2 = c.get("/v1/cfe/lensing?case_id=CACHE-TEST")
    assert r2.status_code == 200
    assert "Cache-Control" in r2.headers and "max-age=120" in r2.headers.get(
        "Cache-Control", ""
    )


def test_cfe_cache_warm_endpoint(monkeypatch) -> None:
    from services.api_gateway.main import app

    monkeypatch.setenv("CFE_CACHE_TTL_SEC", "60")
    c = TestClient(app)
    r = c.post("/v1/cfe/cache/warm", json=["LEX-WARM-1", "LEX-WARM-2"])
    assert r.status_code == 200
    body = r.json()
    assert int(body.get("warmed", 0)) == 2
    assert int(body.get("ttl_sec", 0)) == 60
