#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_marketplace_security.py          |
# | ROLE: Marketplace security tests.                            |
# | PLIK: tests/services/test_marketplace_security.py          |
# | ROLA: Testy bezpieczeństwa Marketplace.                      |
# +-------------------------------------------------------------+
"""
PL: Testy bezpieczeństwa Marketplace: walidacja nazwy wtyczki i endpoint sign (dev-only).
EN: Marketplace security tests: plugin name validation and dev-only sign endpoint.
"""

from __future__ import annotations

import os

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def test_install_rejects_unsafe_name(monkeypatch):
    client = TestClient(app)
    # Minimal poprawny podpis będzie odrzucony — tu interesuje nas nazwa
    body = {"name": "../evil", "manifest_yaml": "module: x", "signature_b64u": "xxx"}
    r = client.post("/v1/marketplace/install", json=body)
    assert r.status_code == 400 and "Invalid plugin name" in r.text


def test_sign_manifest_dev_only(monkeypatch):
    client = TestClient(app)
    # Bez włączenia feature flag — 403
    r = client.post("/v1/marketplace/sign_manifest", json={"manifest_yaml": "name: x"})
    assert r.status_code == 403
    # Po włączeniu flagi i ustawieniu klucza — 200
    monkeypatch.setenv("MARKETPLACE_SIGNING_ENABLED", "1")
    # Użyj tego samego mechanizmu co key_manager (ENV)
    # Wygeneruj parę i ustaw jako ENV (pub do verify pubkey, priv do sign)
    import base64

    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

    sk = Ed25519PrivateKey.generate()
    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")
    os.environ["ED25519_PRIVKEY_PEM"] = pem
    pub = sk.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    os.environ["ED25519_PUBKEY_B64URL"] = base64.urlsafe_b64encode(pub).rstrip(b"=").decode("ascii")

    r2 = client.post("/v1/marketplace/sign_manifest", json={"manifest_yaml": "name: x"})
    assert r2.status_code == 200
    assert "signature_b64url" in r2.json()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
