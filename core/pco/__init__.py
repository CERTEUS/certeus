#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/pco/__init__.py                                |

# | ROLE: Project module.                                       |

# | PLIK: core/pco/__init__.py                                |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from .crypto import (  # noqa: E402
    b64u_decode,
    b64u_encode,
    canonical_bundle_hash_hex,
    canonical_digest_hex,
    compute_leaf_hex,
    ed25519_sign_b64u,
    ed25519_verify_b64u,
    load_pubkey_bytes_from_env,
    sha256_hex,
)
from .merkle import (  # noqa: E402
    MerkleStep,
    apply_merkle_path,
    parse_merkle_proof,
)
from .public_payload import PublicPCO  # noqa: E402

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===




__all__ = [
    "b64u_encode",
    "b64u_decode",
    "sha256_hex",
    "canonical_bundle_hash_hex",
    "compute_leaf_hex",
    "canonical_digest_hex",
    "ed25519_sign_b64u",
    "ed25519_verify_b64u",
    "load_pubkey_bytes_from_env",
    "MerkleStep",
    "parse_merkle_proof",
    "apply_merkle_path",
    "PublicPCO",
]


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
