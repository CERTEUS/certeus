"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: scripts/fix_bom.py                                            |

# | ROLE: Re-save *.json as UTF-8 (no BOM), fixing utf-8-sig            |

# +=====================================================================+

# ----Bloki----- IMPORTY

from __future__ import annotations

import json
import os
from pathlib import Path

# ----Bloki----- MAIN


def main() -> None:
    root = Path(os.getenv("PROOF_BUNDLE_DIR") or "./data/public_pco")

    for p in root.glob("*.json"):
        data = json.loads(p.read_text(encoding="utf-8-sig"))

        p.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

        print(f"fixed: {p}")


if __name__ == "__main__":
    main()
