# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/well_known_jwks.py     |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/well_known_jwks.py     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Endpoint publikujący klucz publiczny Ed25519 w formacie JWKS (/.well-known/jwks.json).

EN: Endpoint exposing Ed25519 public key via JWKS (/.well-known/jwks.json).

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import base64
import hashlib
import os

from fastapi import APIRouter, HTTPException

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


# ----Bloki----- IMPORTY


try:
    from security.key_manager import load_ed25519_public_bytes  # type: ignore

except Exception:  # pragma: no cover
    load_ed25519_public_bytes = None  # type: ignore[assignment]


# ----Bloki----- KONFIGURACJA

router = APIRouter(prefix="", tags=["well-known"])


def _b64u(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def _load_pubkey_bytes() -> bytes:
    backend = os.getenv("KEYS_BACKEND")

    if backend and load_ed25519_public_bytes is not None:
        return load_ed25519_public_bytes()

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


# === I/O / ENDPOINTS ===
@router.get("/.well-known/jwks.json")
# === I/O / ENDPOINTS ===
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


# === TESTY / TESTS ===
