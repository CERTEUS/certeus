#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/security/test_key_manager.py                  |

# | ROLE: Project module.                                       |

# | PLIK: tests/security/test_key_manager.py                  |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

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

from __future__ import annotations

import base64

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from security.key_manager import load_ed25519_private_pem, load_ed25519_public_bytes


def test_key_manager_env_fallback(monkeypatch):
    sk = Ed25519PrivateKey.generate()

    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")

    pk_raw = sk.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )

    monkeypatch.setenv("ED25519_PRIVKEY_PEM", pem)

    monkeypatch.setenv("ED25519_PUBKEY_B64URL", base64.urlsafe_b64encode(pk_raw).rstrip(b"=").decode("ascii"))

    assert load_ed25519_private_pem().startswith("-----BEGIN PRIVATE KEY-----")

    assert load_ed25519_public_bytes() == pk_raw
