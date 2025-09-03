#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_metrics_series.py                |
# | ROLE: Metrics series endpoint test                          |
# | PLIK: tests/services/test_metrics_series.py                |
# | ROLA: Test /v1/metrics/series                                |
# +-------------------------------------------------------------+
"""
PL: Test struktury endpointu /v1/metrics/series.
EN: Tests the structure of /v1/metrics/series endpoint.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_metrics_series_structure() -> None:
    c = TestClient(app)
    r = c.get("/v1/metrics/series?top=3")
    assert r.status_code == 200
    j = r.json()
    assert isinstance(j, dict)
    assert "series" in j
    assert isinstance(j["series"], list)
