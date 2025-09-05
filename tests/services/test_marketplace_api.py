#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_marketplace_api.py               |
# | ROLE: Project test.                                         |
# | PLIK: tests/services/test_marketplace_api.py               |
# | ROLA: Testy API Marketplace (list/verify/install).          |
# +-------------------------------------------------------------+

"""
PL: Testy Marketplace – weryfikacja podpisu i instalacja wtyczki (izolowana).

EN: Marketplace tests – signature verification and plugin install (isolated).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import base64
from pathlib import Path
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient

from services.api_gateway.main import app


def _b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def _gen_keypair() -> tuple[str, bytes]:
    sk = Ed25519PrivateKey.generate()
    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")
    pub = sk.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    return pem, pub


def test_verify_manifest_ok_and_fail(monkeypatch):
    client = TestClient(app)

    pem, pub = _gen_keypair()
    # Skonfiguruj publiczny klucz dla key_manager (ENV)
    monkeypatch.setenv("ED25519_PUBKEY_B64URL", _b64u(pub))

    manifest = """name: signed_demo\nmodule: plugins.signed_demo.src.main\nversion: "0.1.0"\n"""

    # Wygeneruj podpis
    sk = serialization.load_pem_private_key(pem.encode("utf-8"), password=None)
    sig = _b64u(sk.sign(manifest.encode("utf-8")))

    r_ok = client.post(
        "/v1/marketplace/verify_manifest",
        json={"manifest_yaml": manifest, "signature_b64u": sig},
    )
    assert r_ok.status_code == 200 and r_ok.json().get("ok") is True

    r_fail = client.post(
        "/v1/marketplace/verify_manifest",
        json={"manifest_yaml": manifest + "#tamper", "signature_b64u": sig},
    )
    assert r_fail.status_code == 200 and r_fail.json().get("ok") is False


def test_install_writes_to_custom_plugins_dir(tmp_path: Path, monkeypatch):
    client = TestClient(app)

    from services.api_gateway.routers import marketplace as mp

    pem, pub = _gen_keypair()
    monkeypatch.setenv("ED25519_PUBKEY_B64URL", _b64u(pub))

    # Przekieruj katalog pluginów na tmp
    monkeypatch.setattr(mp, "_PLUGINS_DIR", tmp_path)

    manifest = """name: signed_demo\nmodule: plugins.signed_demo.src.main\nversion: "0.1.0"\n"""
    sk = serialization.load_pem_private_key(pem.encode("utf-8"), password=None)
    sig = _b64u(sk.sign(manifest.encode("utf-8")))

    r = client.post(
        "/v1/marketplace/install",
        json={"name": "signed_demo", "manifest_yaml": manifest, "signature_b64u": sig},
    )
    body: dict[str, Any] = r.json()
    assert r.status_code == 200 and body.get("ok") is True

    out = tmp_path / "signed_demo" / "plugin.yaml"
    assert out.exists(), f"plugin.yaml not written to {out}"
