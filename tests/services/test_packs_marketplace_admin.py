#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_packs_marketplace_admin.py       |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_packs_marketplace_admin.py       |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Smoke admin API Marketplace (install/enable/list/details/try).
EN: Marketplace admin API smoke (install/enable/list/details/try).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_install_enable_list_and_details_roundtrip() -> None:
    c = TestClient(app)
    # List packs
    r0 = c.get("/v1/packs/")
    assert r0.status_code == 200
    packs = r0.json()
    assert isinstance(packs, list)
    if not packs:
        return  # no packs in this repo snapshot; skip rest
    name = packs[0]["name"]

    # Install with signature (stub) and optional version
    sig = "A" * 64
    r1 = c.post("/v1/packs/install", json={"pack": name, "signature": sig, "version": "1.0.0"})
    assert r1.status_code == 200
    body1 = r1.json()
    assert body1.get("ok") is True and body1.get("signature") is True

    # Enable explicitly
    r2 = c.post("/v1/packs/enable", json={"pack": name, "enabled": True})
    assert r2.status_code == 200 and r2.json().get("enabled") is True

    # Details reflect enabled + manifest present
    r3 = c.get(f"/v1/packs/{name}")
    assert r3.status_code == 200
    det = r3.json()
    assert det.get("name") == name
    assert isinstance(det.get("manifest"), dict)

    # Try invocation (best-effort) — should not 5xx
    r4 = c.post("/v1/packs/try", json={"pack": name, "payload": {}})
    assert r4.status_code == 200
