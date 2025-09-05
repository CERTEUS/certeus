#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_no_store_mutating_global.py      |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_no_store_mutating_global.py      |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Globalne no-store — POST na kluczowych mutujących endpointach.
EN: Global no-store — POST on key mutating endpoints.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_global_no_store_headers() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    r1 = c.post("/v1/devices/horizon_drive/plan", json={})
    assert r1.status_code == 200
    assert r1.headers.get("Cache-Control") == "no-store"

    r2 = c.post("/v1/mailops/ingest", json={"mail_id": "m1", "from_addr": "a@b", "to": []})
    assert r2.status_code == 200
    assert r2.headers.get("Cache-Control") == "no-store"

    r3 = c.post("/v1/export", json={"case_id": "C-1", "analysis_result": {"ok": True}})
    assert r3.status_code == 200
    assert r3.headers.get("Cache-Control") == "no-store"
