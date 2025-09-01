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


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: runtime/pco_encryptor.py                                      |

# | ROLE:                                                               |

# |  PL: Szyfrowanie kopertowe PCO (AES-GCM; DEK z KMS/Vault).          |

# |  EN: PCO envelope encryption (AES-GCM; DEK via KMS/Vault).          |

# +=====================================================================+

from __future__ import annotations

from os import urandom

from cryptography.hazmat.primitives.ciphers.aead import AESGCM  # type: ignore


def new_dek() -> bytes:
    """

    PL: Wygeneruj 256-bitowy klucz danych (DEK).

    EN: Generate a 256-bit data-encryption key (DEK).

    """

    return urandom(32)


def encrypt(dek: bytes, plaintext: bytes, aad: bytes = b"") -> tuple[bytes, bytes, bytes]:
    """

    PL: Zaszyfruj AES-GCM: zwróć (iv, ciphertext, aad).

    EN: AES-GCM encrypt: return (iv, ciphertext, aad).

    """

    iv = urandom(12)  # 96-bit IV for AES-GCM

    ct = AESGCM(dek).encrypt(iv, plaintext, aad)

    return iv, ct, aad


def decrypt(dek: bytes, iv: bytes, ct: bytes, aad: bytes = b"") -> bytes:
    """

    PL: Odszyfruj AES-GCM.

    EN: AES-GCM decrypt.

    """

    return AESGCM(dek).decrypt(iv, ct, aad)
