# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/pem_to_b64url.py                            |

# | ROLE: Project module.                                       |

# | PLIK: scripts/pem_to_b64url.py                            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

# +======================================================================+

# |                               CERTEUS                                |

# +======================================================================+

# | FILE / PLIK: scripts/pem_to_b64url.py                                |

# | ROLA / ROLE:                                                          |

# |  PL: Konwersja PEM Ed25519 (public) -> Base64URL (pole 'x' do JWKS).  |

# |  EN: Convert Ed25519 public PEM -> Base64URL (JWKS 'x' value).        |

# +======================================================================+

# Opis:

# - Wczytuje klucz publiczny Ed25519 w PEM i wypisuje Base64URL bez '='.

# Użycie:

#   uv run python scripts/pem_to_b64url.py --in ed25519-public.pem

# Wymagania:

#   - Python 3.11+, cryptography

# ----Bloki----- IMPORTY

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import base64
from pathlib import Path

from cryptography.hazmat.primitives import serialization

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# ----Bloki----- MAIN

def main() -> None:
    ap = argparse.ArgumentParser()

    ap.add_argument("--in", dest="inp", required=True)

    args = ap.parse_args()

    raw = Path(args.inp).read_bytes()

    pk = serialization.load_pem_public_key(raw)

    # Ed25519 only:

    b = pk.public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )

    print(base64.urlsafe_b64encode(b).rstrip(b"=").decode())

if __name__ == "__main__":
    main()

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
