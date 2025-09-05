#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/pco/crypto.py                                  |

# | ROLE: Project module.                                       |

# | PLIK: core/pco/crypto.py                                  |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Krypto-pomocniki: sha256 (kanoniczne), b64url, Ed25519 (podpis/weryfikacja).

EN: Crypto helpers: canonical sha256, b64url, Ed25519 sign/verify.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import base64
import hashlib
import json
import os
from typing import Any

from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# ----Bloki----- IMPORTY

# ----Bloki----- B64URL

def b64u_encode(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")

def b64u_decode(s: str) -> bytes:
    s = s.strip()

    s = s + "==="[: (4 - len(s) % 4) % 4]

    return base64.urlsafe_b64decode(s.encode("ascii"))

# ----Bloki----- HASH

def sha256_hex(data: bytes | str) -> str:
    if isinstance(data, str):
        data = data.encode("utf-8")

    return hashlib.sha256(data).hexdigest()

def _lfsc_sha256(lfsc_text: str) -> str:
    return sha256_hex(lfsc_text)

def _drat_sha256_maybe(drat_text: str | None) -> str | None:
    return None if drat_text is None else sha256_hex(drat_text)

def canonical_bundle_hash_hex(
    smt2_hash_hex: str,
    lfsc_text: str,
    drat_text: str | None = None,
) -> str:
    """

    EN/PL: Canonical bundle hash = SHA256(JSON({lfsc_sha256, smt2_hash[, drat_sha256]})),

           where JSON is compact and key-sorted (separators=(',', ':'), sort_keys=True).

    """

    payload: dict[str, str] = {
        "lfsc_sha256": _lfsc_sha256(lfsc_text),
        "smt2_hash": smt2_hash_hex.lower(),
    }

    drat = _drat_sha256_maybe(drat_text)

    if drat is not None:
        payload["drat_sha256"] = drat

    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")

    return sha256_hex(blob)

def compute_leaf_hex(rid: str, bundle_hash_hex: str) -> str:
    """

    EN/PL: Leaf = sha256( sha256(rid) || bundle_hash ).

    """

    rid_hash = hashlib.sha256(rid.encode("utf-8")).digest()

    bundle_hash = bytes.fromhex(bundle_hash_hex)

    return hashlib.sha256(rid_hash + bundle_hash).hexdigest()

def canonical_digest_hex(
    *,
    rid: str,
    smt2_hash_hex: str,
    lfsc_text: str,
    merkle_root_hex: str,
    drat_text: str | None = None,
) -> str:
    """

    EN/PL: Canonical digest over public payload parts:

      sha256(

        sha256(rid) ||

        smt2_hash ||

        sha256(lfsc) ||

        [sha256(drat)?] ||

        merkle_root

      )

    """

    parts_hex: list[str] = [
        sha256_hex(rid.encode("utf-8")),
        smt2_hash_hex.lower(),
        _lfsc_sha256(lfsc_text),
    ]

    drat = _drat_sha256_maybe(drat_text)

    if drat is not None:
        parts_hex.append(drat)

    parts_hex.append(merkle_root_hex.lower())

    data = b"".join(bytes.fromhex(h) for h in parts_hex)

    return sha256_hex(data)

# ----Bloki----- Ed25519

def ed25519_sign_b64u(private_key_bytes: bytes, msg_hex: str) -> str:
    sk = Ed25519PrivateKey.from_private_bytes(private_key_bytes)

    sig = sk.sign(bytes.fromhex(msg_hex))

    return b64u_encode(sig)

def ed25519_verify_b64u(public_key_bytes: bytes, signature_b64u: str, msg_hex: str) -> None:
    pk = Ed25519PublicKey.from_public_bytes(public_key_bytes)

    # raises InvalidSignature on failure

    pk.verify(b64u_decode(signature_b64u), bytes.fromhex(msg_hex))

def _is_ed25519_jwk(k: dict[str, Any], kid: str | None = None) -> bool:
    """Czy wpis JWK to OKP/Ed25519 z opcjonalnym dopasowaniem kid i z kluczem 'x'."""

    if kid is not None and k.get("kid") != kid:
        return False

    return k.get("kty") == "OKP" and k.get("crv") == "Ed25519" and "x" in k

def load_pubkey_bytes_from_env() -> bytes:
    """

    Priority:

      1) ED25519_PUBKEY_HEX

      2) ED25519_PUBKEY_B64URL (or ED25519_PUBKEY_B64U)

      3) PCO_JWKS_B64URL (+ optional PCO_ACTIVE_KID)

    """

    # 1) Raw hex in env (tests rely on this)

    key_hex = os.getenv("ED25519_PUBKEY_HEX")

    if key_hex:
        return bytes.fromhex(key_hex.strip())

    # 2) Raw b64url in env

    key_b64u = os.getenv("ED25519_PUBKEY_B64URL") or os.getenv("ED25519_PUBKEY_B64U")

    if key_b64u:
        return b64u_decode(key_b64u)

    # 3) JWKS (b64url-encoded in env)

    jwks_b64 = os.getenv("PCO_JWKS_B64URL")

    if jwks_b64:
        jwks = json.loads(b64u_decode(jwks_b64).decode("utf-8"))

        kid = os.getenv("PCO_ACTIVE_KID")

        if kid:
            for k in jwks.get("keys", []):
                if _is_ed25519_jwk(k, kid=kid):
                    return b64u_decode(k["x"])

        for k in jwks.get("keys", []):
            if _is_ed25519_jwk(k):
                return b64u_decode(k["x"])

    raise RuntimeError(
        "No Ed25519 public key configured. "
        "Set PCO_JWKS_B64URL+PCO_ACTIVE_KID or ED25519_PUBKEY_HEX or "
        "ED25519_PUBKEY_B64URL."
    )

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
