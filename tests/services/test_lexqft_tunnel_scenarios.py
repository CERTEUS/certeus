#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_tunnel_scenarios.py       |
# | ROLE: LexQFT tunnel scenarios (barrier catalog)            |
# | PLIK: tests/services/test_lexqft_tunnel_scenarios.py       |
# | ROLA: Scenariusze tunelowania (katalog barier)            |
# +-------------------------------------------------------------+

"""
PL: Testy scenariuszy tunelowania: katalog barier i zachowanie dla 'thick'.
EN: Tunnel scenarios tests: barrier catalog and behavior for 'thick'.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_barrier_scenarios_listed() -> None:
    r = client.get("/v1/lexqft/tunnel/scenarios")
    assert r.status_code == 200
    arr = r.json()
    assert isinstance(arr, list) and len(arr) >= 3
    ids = {x["model_id"] for x in arr}
    assert {"thin", "thick", "stepped"}.issubset(ids)


def test_thick_barrier_reflects_at_low_energy() -> None:
    # reset log file for deterministic check
    from services.api_gateway.routers.lexqft import _TUNNEL_LOG  # type: ignore

    try:
        Path(_TUNNEL_LOG).unlink(missing_ok=True)  # type: ignore[arg-type]
    except Exception:
        pass
    # thick barrier has energy=1.5; evidence=1.0 should yield reflect path
    r = client.post(
        "/v1/lexqft/tunnel",
        json={
            "state_uri": "lexqft-case-2",
            "evidence_energy": 1.0,
            "barrier_model": {"energy": 1.5, "model_uri": "lexqft://barrier/thick"},
            "counter_arguments": ["low_energy", "no_shortcut"],
        },
    )
    assert r.status_code == 200
    body = r.json()
    assert body["path"][-1] == "reflect"
    # PCO includes model_uri header when provided
    assert (
        r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.model_uri")
        == "lexqft://barrier/thick"
    )
    # log file should have one line
    try:
        with Path(_TUNNEL_LOG).open("r", encoding="utf-8") as fh:  # type: ignore[arg-type]
            lines = [ln for ln in fh.read().splitlines() if ln.strip()]
            assert len(lines) == 1
    except FileNotFoundError:
        # acceptable on platforms without fs perms in CI
        pass
