#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_horizon_lensing.py           |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_horizon_lensing.py           |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy deterministycznego horyzontu (masa) i lensingu per case.
EN: Deterministic horizon (mass) and lensing per case tests.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_cfe_horizon_and_lensing_deterministic() -> None:
    from services.api_gateway.main import app

    client = TestClient(app)
    cid = "LEX-DET-002"

    h1 = client.post("/v1/cfe/horizon", json={"case": cid, "lock": True})
    h2 = client.post("/v1/cfe/horizon", json={"case": cid, "lock": True})
    assert h1.status_code == 200 and h2.status_code == 200
    m1 = float(h1.json()["horizon_mass"])  # type: ignore[index]
    m2 = float(h2.json()["horizon_mass"])  # type: ignore[index]
    assert 0.05 <= m1 <= 0.95
    assert m1 == m2  # deterministic per case

    l1 = client.get(f"/v1/cfe/lensing?case_id={cid}")
    l2 = client.get(f"/v1/cfe/lensing?case_id={cid}")
    assert l1.status_code == 200 and l2.status_code == 200
    assert l1.json()["lensing_map"] == l2.json()["lensing_map"]  # deterministic
    assert len(l1.json()["critical_precedents"]) >= 1
