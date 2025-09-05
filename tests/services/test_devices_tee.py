#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_devices_tee.py                   |
# | ROLE: Devices TEE RA signalling tests                        |
# | PLIK: tests/services/test_devices_tee.py                   |
# | ROLA: Testy sygnalizacji TEE/RA w urządzeniach               |
# +-------------------------------------------------------------+

"""
PL: W10 — gdy `TEE_ENABLED=1`, urządzenia dodają nagłówek `X-CERTEUS-TEE-RA`.

EN: W10 — when `TEE_ENABLED=1`, devices attach `X-CERTEUS-TEE-RA` header.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json

from fastapi.testclient import TestClient


def test_devices_attach_tee_ra_header(monkeypatch) -> None:
    # enable tee
    monkeypatch.setenv("TEE_ENABLED", "1")
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post("/v1/devices/qoracle/expectation", json={"question": "W10 test"})
    assert r.status_code == 200
    hdr = r.headers.get("X-CERTEUS-TEE-RA")
    assert isinstance(hdr, str) and hdr
    data = json.loads(hdr)
    assert "fingerprint" in data and isinstance(data["fingerprint"], str)
