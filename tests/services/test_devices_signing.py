#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_devices_signing.py               |
# | ROLE: Devices output signing tests                           |
# | PLIK: tests/services/test_devices_signing.py               |
# | ROLA: Testy podpisów wyjść urządzeń                          |
# +-------------------------------------------------------------+

"""
PL: W9 — sprawdza, że wyjście urządzenia jest podpisane (nagłówek JSON) i
    podpis weryfikuje się względem kanonicznego JSON ciała odpowiedzi.

EN: W9 — verifies device output signature (JSON header) and that the signature
    validates against the canonical JSON of the response body.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import base64
import json
import os

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)
from fastapi.testclient import TestClient


def _gen_keys_env() -> tuple[str, bytes]:
    sk = Ed25519PrivateKey.generate()
    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")
    pub = sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)
    os.environ["ED25519_PRIVKEY_PEM"] = pem
    os.environ["ED25519_PUBKEY_HEX"] = pub.hex()
    return pem, pub


def _canon_bytes(d: dict) -> bytes:
    return json.dumps(d, sort_keys=True, separators=(",", ":")).encode("utf-8")


def test_hde_plan_signature_header_verifies() -> None:
    # Prepare keys in ENV before importing app
    _gen_keys_env()

    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post("/v1/devices/horizon_drive/plan", json={"target_horizon": 0.2})
    assert r.status_code == 200
    hdr = r.headers.get("X-CERTEUS-SIG-device")
    assert isinstance(hdr, str) and hdr
    meta = json.loads(hdr)
    assert meta.get("alg") == "EdDSA" and isinstance(meta.get("sig"), str)
    # Verify signature against canonical JSON of the response body
    body = r.json()
    sig_b64u: str = meta["sig"]
    pad = "=" * (-len(sig_b64u) % 4)
    sig = base64.urlsafe_b64decode(sig_b64u + pad)
    pub_hex = os.environ.get("ED25519_PUBKEY_HEX", "")
    pub = Ed25519PublicKey.from_public_bytes(bytes.fromhex(pub_hex))
    pub.verify(sig, _canon_bytes(body))
