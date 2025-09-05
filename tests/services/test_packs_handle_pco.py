#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_packs_handle_pco.py              |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_packs_handle_pco.py              |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy /v1/packs/handle dla nowych packów (MED/SEC/CODE) z minimalnym PCO.
EN: Tests for /v1/packs/handle for new packs (MED/SEC/CODE) with minimal PCO.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def _assert_pco_present(body: dict) -> None:
    assert body.get("ok") is True
    res = body.get("result")
    assert isinstance(res, dict)
    val = res.get("pco") or body.get("pco")
    assert isinstance(val, dict)


def test_packs_handle_med_summary_returns_pco() -> None:
    c = TestClient(app)
    r = c.post(
        "/v1/packs/handle",
        json={
            "pack": "plugins.packs_med.src.main",
            "kind": "case.summary",
            "payload": {"subject": "MED-1", "risk_index": 0.2},
        },
    )
    assert r.status_code == 200
    _assert_pco_present(r.json())


def test_packs_handle_sec_policy_audit_returns_pco() -> None:
    c = TestClient(app)
    r = c.post(
        "/v1/packs/handle",
        json={
            "pack": "plugins.packs_sec.src.main",
            "kind": "policy.audit",
            "payload": {"policy": {"name": "P", "required": ["a"], "provided": ["a"]}},
        },
    )
    assert r.status_code == 200
    _assert_pco_present(r.json())


def test_packs_handle_code_normalize_returns_pco() -> None:
    c = TestClient(app)
    r = c.post(
        "/v1/packs/handle",
        json={
            "pack": "plugins.packs_code.src.main",
            "kind": "text.normalize",
            "payload": {"text": " a   b  c "},
        },
    )
    assert r.status_code == 200
    _assert_pco_present(r.json())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
