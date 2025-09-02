"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: security/key_manager.py                             |

# | ROLE: Project module.                                       |

# | PLIK: security/key_manager.py                             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from __future__ import annotations

import base64
import os

import requests


def _b64u(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def load_ed25519_public_bytes() -> bytes:
    backend = os.getenv("KEYS_BACKEND", "env").lower()

    if backend == "vault":
        addr = os.getenv("VAULT_ADDR")

        token = os.getenv("VAULT_TOKEN")

        secret_path = os.getenv("VAULT_SECRET_PATH")

        if not (addr and token and secret_path):
            raise RuntimeError("Missing VAULT_* configuration for KEYS_BACKEND=vault")

        url = addr.rstrip("/") + "/v1/" + secret_path.lstrip("/")

        r = requests.get(url, headers={"X-Vault-Token": token}, timeout=10)

        r.raise_for_status()

        data = r.json().get("data", {}).get("data", {})

        b64u = data.get("ed25519_pubkey_b64url")

        if not b64u:
            raise RuntimeError("Vault secret missing 'ed25519_pubkey_b64url'")

        pad = "=" * (-len(b64u) % 4)

        return base64.urlsafe_b64decode(b64u + pad)

    # ENV fallback

    b64u = os.getenv("ED25519_PUBKEY_B64URL")

    if b64u:
        pad = "=" * (-len(b64u) % 4)

        return base64.urlsafe_b64decode(b64u + pad)

    hexv = os.getenv("ED25519_PUBKEY_HEX")

    if hexv:
        return bytes.fromhex(hexv)

    raise RuntimeError("No public key configured")


def load_ed25519_private_pem() -> str:
    backend = os.getenv("KEYS_BACKEND", "env").lower()

    if backend == "vault":
        addr = os.getenv("VAULT_ADDR")

        token = os.getenv("VAULT_TOKEN")

        secret_path = os.getenv("VAULT_SECRET_PATH")

        if not (addr and token and secret_path):
            raise RuntimeError("Missing VAULT_* configuration for KEYS_BACKEND=vault")

        url = addr.rstrip("/") + "/v1/" + secret_path.lstrip("/")

        r = requests.get(url, headers={"X-Vault-Token": token}, timeout=10)

        r.raise_for_status()

        data = r.json().get("data", {}).get("data", {})

        pem = data.get("ed25519_privkey_pem")

        if not pem:
            raise RuntimeError("Vault secret missing 'ed25519_privkey_pem'")

        return pem

    # ENV/file fallback

    pem_env = os.getenv("ED25519_PRIVKEY_PEM")

    if pem_env and "BEGIN" in pem_env:
        return pem_env

    pem_path = os.getenv("ED25519_PRIVKEY_PEM_PATH")

    if pem_path and os.path.exists(pem_path):
        return open(pem_path, encoding="utf-8").read()

    raise RuntimeError("No private key configured")
