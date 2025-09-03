#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_metrics_summary.py               |
# | ROLE: Quick metrics summary endpoint test                   |
# | PLIK: tests/services/test_metrics_summary.py               |
# | ROLA: Test endpointu /v1/metrics/summary                    |
# +-------------------------------------------------------------+
"""
PL: Minimalny test zwracania struktury podsumowania metryk.
EN: Minimal test for returning metrics summary structure.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_metrics_summary_structure() -> None:
    c = TestClient(app)
    r = c.get("/v1/metrics/summary")
    assert r.status_code == 200
    j = r.json()
    assert "top_avg_ms" in j and "top_count" in j and "total_paths" in j
    assert isinstance(j["top_avg_ms"], list)
    assert isinstance(j["top_count"], list)
