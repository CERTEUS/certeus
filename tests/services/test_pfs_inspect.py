#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_inspect.py                  |
# | ROLE: ProofFS inspection tests                               |
# | PLIK: tests/services/test_pfs_inspect.py                  |
# | ROLA: Testy inspekcji ProofFS                                |
# +-------------------------------------------------------------+
"""
PL: W7 — ProofFS read-only: po tunelowaniu ścieżka pojawia się w PFS.
EN: W7 — ProofFS read-only: after tunneling, path is visible in PFS.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_pfs_inspect_after_tunnel() -> None:
    case = "pfs-demo-1"
    r = client.post(
        "/v1/lexqft/tunnel",
        json={
            "state_uri": case,
            "evidence_energy": 1.1,
            "barrier_model": {"V0": 1.0, "w": 2.0, "m": 1.0},
        },
    )
    assert r.status_code == 200

    r2 = client.get(f"/v1/pfs/case/{case}")
    assert r2.status_code == 200
    paths = r2.json().get("paths") or []
    assert isinstance(paths, list) and len(paths) >= 1
    assert all(isinstance(p, list) for p in paths)

    r3 = client.get("/v1/pfs/inspect")
    assert r3.status_code == 200
    body = r3.json()
    assert case in (body.get("cases") or [])
