# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/fix_bom.py                                  |

# | ROLE: Project module.                                       |

# | PLIK: scripts/fix_bom.py                                  |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Moduł projektu CERTEUS (uogólniony opis).



EN: CERTEUS project module (generic description).

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


# +=====================================================================+


# |                              CERTEUS                                |


# +=====================================================================+


# | FILE: scripts/fix_bom.py                                            |


# | ROLE: Re-save *.json as UTF-8 (no BOM), fixing utf-8-sig            |


# +=====================================================================+


# ----Bloki----- IMPORTY


# ----Bloki----- MAIN


def main() -> None:
    root = Path(os.getenv("PROOF_BUNDLE_DIR") or "./data/public_pco")

    for p in root.glob("*.json"):
        data = json.loads(p.read_text(encoding="utf-8-sig"))

        p.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

        print(f"fixed: {p}")


if __name__ == "__main__":
    main()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
