#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_devices_idempotency.py           |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_devices_idempotency.py           |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy idempotency header dla devices: HDE/Q-Oracle/Entangle/Chronosync.
EN: Idempotency header tests for devices: HDE/Q-Oracle/Entangle/Chronosync.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def _assert_replay_headers(h1: str | None, h2: str | None) -> None:
    assert h1 in {"0", None}  # first may be explicitly "0" or absent
    assert h2 == "1"


def test_hde_idempotent_replay_flag() -> None:
    c = TestClient(app)
    key = "idem-abc-1"
    r1 = c.post("/v1/devices/horizon_drive/plan", json={}, headers={"X-Idempotency-Key": key})
    r2 = c.post("/v1/devices/horizon_drive/plan", json={}, headers={"X-Idempotency-Key": key})
    assert r1.status_code == r2.status_code == 200
    assert r1.json() == r2.json()
    _assert_replay_headers(r1.headers.get("X-Idempotent-Replay"), r2.headers.get("X-Idempotent-Replay"))


def test_qoracle_idempotent_replay_flag() -> None:
    c = TestClient(app)
    key = "idem-abc-2"
    r1 = c.post(
        "/v1/devices/qoracle/expectation",
        json={"question": "maximize outcome", "constraints": {"limit": 10}},
        headers={"X-Idempotency-Key": key},
    )
    r2 = c.post(
        "/v1/devices/qoracle/expectation",
        json={"question": "maximize outcome", "constraints": {"limit": 10}},
        headers={"X-Idempotency-Key": key},
    )
    assert r1.status_code == r2.status_code == 200
    assert r1.json() == r2.json()
    _assert_replay_headers(r1.headers.get("X-Idempotent-Replay"), r2.headers.get("X-Idempotent-Replay"))


def test_entangle_idempotent_replay_flag() -> None:
    c = TestClient(app)
    key = "idem-abc-3"
    body = {"variables": ["A", "B", "C"], "target_negativity": 0.1}
    r1 = c.post("/v1/devices/entangle", json=body, headers={"X-Idempotency-Key": key})
    r2 = c.post("/v1/devices/entangle", json=body, headers={"X-Idempotency-Key": key})
    assert r1.status_code == r2.status_code == 200
    assert r1.json() == r2.json()
    _assert_replay_headers(r1.headers.get("X-Idempotent-Replay"), r2.headers.get("X-Idempotent-Replay"))


def test_chronosync_idempotent_replay_flag() -> None:
    c = TestClient(app)
    key = "idem-abc-4"
    body = {"coords": {"a": 1}, "pc_delta": {"x": 1}}
    r1 = c.post("/v1/devices/chronosync/reconcile", json=body, headers={"X-Idempotency-Key": key})
    r2 = c.post("/v1/devices/chronosync/reconcile", json=body, headers={"X-Idempotency-Key": key})
    assert r1.status_code == r2.status_code == 200
    assert r1.json() == r2.json()
    _assert_replay_headers(r1.headers.get("X-Idempotent-Replay"), r2.headers.get("X-Idempotent-Replay"))


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
