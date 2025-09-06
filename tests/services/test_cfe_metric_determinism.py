#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_metric_determinism.py        |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_metric_determinism.py        |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Sprawdza deterministyczność `kappa_max` i geodezyjnej per `case_id`.
EN: Checks determinism of `kappa_max` and geodesic per `case_id`.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_cfe_curvature_and_geodesic_deterministic() -> None:
    from services.api_gateway.main import app

    client = TestClient(app)

    cid = "LEX-DET-001"

    r1 = client.get(f"/v1/cfe/curvature?case_id={cid}")
    r2 = client.get(f"/v1/cfe/curvature?case_id={cid}")
    assert r1.status_code == 200 and r2.status_code == 200
    assert float(r1.json()["kappa_max"]) == float(r2.json()["kappa_max"])  # deterministic

    g1 = client.post("/v1/cfe/geodesic", json={"case": cid})
    g2 = client.post("/v1/cfe/geodesic", json={"case": cid})
    assert g1.status_code == 200 and g2.status_code == 200
    assert g1.json()["path"] == g2.json()["path"]
    assert float(g1.json()["geodesic_action"]) == float(g2.json()["geodesic_action"])  # deterministic
