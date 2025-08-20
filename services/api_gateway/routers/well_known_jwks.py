# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | MODULE: services/api_gateway/routers/.well_known_jwks.py            |
# | DATE:   2025-08-19                                                  |
# +=====================================================================+
"""
PL: Endpoint publikujący klucz publiczny Ed25519 w formacie JWKS (/.well-known/jwks.json).
EN: Endpoint exposing Ed25519 public key via JWKS (/.well-known/jwks.json).
"""

# ----Bloki----- IMPORTY
from __future__ import annotations

import base64
import hashlib
import os

from fastapi import APIRouter, HTTPException

# ----Bloki----- KONFIGURACJA
router = APIRouter(prefix="", tags=["well-known"])


def _b64u(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def _load_pubkey_bytes() -> bytes:
    b64u = os.getenv("ED25519_PUBKEY_B64URL")
    if b64u:
        pad = "=" * (-len(b64u) % 4)
        return base64.urlsafe_b64decode(b64u + pad)
    hexv = os.getenv("ED25519_PUBKEY_HEX")
    if hexv:
        return bytes.fromhex(hexv)
    raise RuntimeError("Brak klucza publicznego: ustaw ED25519_PUBKEY_B64URL lub ED25519_PUBKEY_HEX")


def _kid_from_key(pub: bytes) -> str:
    return hashlib.sha256(pub).hexdigest()[:16]


# ----Bloki----- ENTRYPOINT
@router.get("/.well-known/jwks.json")
def jwks():
    try:
        pub = _load_pubkey_bytes()
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e)) from e
    kid = _kid_from_key(pub)
    jwk = {
        "kty": "OKP",
        "crv": "Ed25519",
        "x": _b64u(pub),
        "kid": kid,
        "use": "sig",
        "alg": "EdDSA",
    }
    return {"keys": [jwk]}
