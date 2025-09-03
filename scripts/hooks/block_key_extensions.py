#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/hooks/block_key_extensions.py               |

# | ROLE: Project module.                                       |

# | PLIK: scripts/hooks/block_key_extensions.py               |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import sys

# === KONFIGURACJA / CONFIGURATION ===

FORBIDDEN_EXT = {".pem", ".key", ".der", ".pfx", ".p12"}

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# +=============================================================+

# |                      CERTEUS — GUARD                        |

# +=============================================================+

# | FILE: scripts/hooks/block_key_extensions.py                 |

# | ROLE: Block committing key material by extension.           |

# | NOTE: Used by pre-commit. Fails commit if any staged file   |

# |       matches forbidden extensions (pem,key,der,pfx,p12).   |

# +=============================================================+


def main(argv: list[str]) -> int:
    bad: list[str] = []

    for a in argv:
        p = Path(a)

        if p.suffix.lower() in FORBIDDEN_EXT:
            bad.append(str(p))

    if bad:
        print("⛔  BLOCKED: key material must not be committed:")

        for b in bad:
            print(f"   - {b}")

        print("\nHint: keep keys local; use env/JWKS or secrets manager instead.")

        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
