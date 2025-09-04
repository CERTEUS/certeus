#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_shedder_adaptive.py              |
# | ROLE: Test adaptive load shedding (forced rate)              |
# | PLIK: tests/services/test_shedder_adaptive.py              |
# | ROLA: Test adaptacyjnego sheddera (wymuszony rate)           |
# +-------------------------------------------------------------+
"""
PL: Sprawdza, że po włączeniu `SHED_ENABLE=1` i wymuszeniu `SHED_FORCE_RATE=1`
    wybrane żądania ciężkie są shedowane (503). Test odporny na brak OTel.

EN: Verifies that with `SHED_ENABLE=1` and `SHED_FORCE_RATE=1` heavy requests
    are shed (503). Test is OTel-agnostic.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_adaptive_shedder_forces_503(monkeypatch) -> None:
    monkeypatch.setenv("SHED_ENABLE", "1")
    monkeypatch.setenv("SHED_FORCE_RATE", "1.0")
    monkeypatch.setenv("SHED_MAX_RATE", "1.0")
    from services.api_gateway.main import app

    client = TestClient(app)
    r = client.post("/v1/qtm/measure", json={"operator": "L", "source": "shed-test"})
    assert r.status_code in {503, 429}  # 429 if limits kick in first
