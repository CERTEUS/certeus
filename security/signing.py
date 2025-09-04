#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: security/signing.py                                  |
# | ROLE: Ed25519 signing helpers (device outputs)               |
# | PLIK: security/signing.py                                  |
# | ROLA: Pomocnicze funkcje podpisu Ed25519 (wyjścia Devices)   |
# +-------------------------------------------------------------+

"""
PL: Narzędzia do podpisywania ładunków JSON (kanonicznych) kluczem Ed25519.

EN: Utilities for signing canonical JSON payloads with Ed25519.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import hashlib
import json
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from .key_manager import load_ed25519_private_pem, load_ed25519_public_bytes


def _canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _kid_from_pub(pub: bytes) -> str:
    # first 12 hex chars as kid suffix
    return "kid-" + pub.hex()[:12]


def sign_payload(payload: dict[str, Any]) -> dict[str, str]:
    """Sign dict payload (canonical JSON) and return signature metadata.

    Returns { alg, kid, payload_hash, sig } with base64url signature.
    """

    pem = load_ed25519_private_pem()
    sk = serialization.load_pem_private_key(pem.encode("utf-8"), password=None)
    assert isinstance(sk, Ed25519PrivateKey)
    canon = _canonical_json_bytes(payload)
    sig = sk.sign(canon)
    pub = load_ed25519_public_bytes()
    h = hashlib.sha256(canon).hexdigest()
    import base64

    b64u = base64.urlsafe_b64encode(sig).rstrip(b"=").decode("ascii")
    return {
        "alg": "EdDSA",
        "kid": _kid_from_pub(pub),
        "payload_hash": f"sha256:{h}",
        "canon": "json/sort_keys=true;separators=',' ':'",
        "sig": b64u,
    }
