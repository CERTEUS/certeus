#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_packs_install_hex_validation.py  |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_packs_install_hex_validation.py  |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Walidacja podpisu w /v1/packs/install — niehex 64 znaki → 400.
EN: Signature validation in /v1/packs/install — non-hex 64 chars -> 400.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_install_signature_must_be_hex_64() -> None:
    c = TestClient(app)
    r = c.get("/v1/packs/")
    assert r.status_code == 200
    packs = r.json()
    assert packs, "Brak paczek do testu"
    name = packs[0]["name"]

    # Non-hex 64 chars (z) should fail
    sig = "z" * 64
    r2 = c.post("/v1/packs/install", json={"pack": name, "signature": sig})
    assert r2.status_code == 400

    # Valid hex 64 chars should pass
    ok_sig = "a1" * 32  # 64 hex chars
    r3 = c.post(
        "/v1/packs/install",
        json={"pack": name, "signature": ok_sig, "version": "1.0.0"},
    )
    assert r3.status_code == 200


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
