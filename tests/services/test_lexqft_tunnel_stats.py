#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_tunnel_stats.py           |
# | ROLE: LexQFT tunnel stats endpoint tests                   |
# | PLIK: tests/services/test_lexqft_tunnel_stats.py           |
# | ROLA: Testy endpointu statystyk tunelowania                |
# +-------------------------------------------------------------+

"""
PL: Test statystyk tunelowania: reset logu -> 2 wywołania -> count=2.
EN: Tunnel stats test: reset log -> 2 calls -> count=2.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_tunnel_stats_counts_events() -> None:
    from services.api_gateway.routers.lexqft import _TUNNEL_LOG  # type: ignore

    try:
        Path(_TUNNEL_LOG).unlink(missing_ok=True)  # type: ignore[arg-type]
    except Exception:
        pass

    for _ in range(2):
        r = client.post(
            "/v1/lexqft/tunnel",
            json={"evidence_energy": 1.2, "state_uri": "stats-case"},
        )
        assert r.status_code == 200

    rs = client.get("/v1/lexqft/tunnel/stats")
    assert rs.status_code == 200
    body = rs.json()
    assert int(body.get("count", 0)) >= 2
    # last_ts should be present
    assert body.get("last_ts")
