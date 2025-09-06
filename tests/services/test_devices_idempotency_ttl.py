#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_devices_idempotency_ttl.py       |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_devices_idempotency_ttl.py       |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Test TTL dla idempotency (IDEMP_TTL_SEC=0 -> brak replay, nagłówek '0').
EN: TTL test for idempotency (IDEMP_TTL_SEC=0 -> no replay, header '0').
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_idempotency_ttl_zero_disables_replay(monkeypatch) -> None:
    # Force TTL=0 for this test
    monkeypatch.setenv("IDEMP_TTL_SEC", "0")
    c = TestClient(app)
    key = "idem-ttl-0"
    r1 = c.post(
        "/v1/devices/horizon_drive/plan",
        json={"target_horizon": 0.2},
        headers={"X-Idempotency-Key": key},
    )
    r2 = c.post(
        "/v1/devices/horizon_drive/plan",
        json={"target_horizon": 0.2},
        headers={"X-Idempotency-Key": key},
    )
    assert r1.status_code == r2.status_code == 200
    # With TTL=0, the second call should not be served from cache
    assert r2.headers.get("X-Idempotent-Replay") == "0"
    # Cleanup env (pytest monkeypatch will undo automatically)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
