# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/lexlog_eval_smoke_fallback.py               |

# | ROLE: Project module.                                       |

# | PLIK: scripts/lexlog_eval_smoke_fallback.py               |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

CERTEUS — Lexlog Smoke Eval (Fallback)

PL: Skrypt pomocniczy budujący plik flag (na podstawie mappingu) i

    uruchamiający test dymny oceny LEXLOG (art. 286 k.k.).

EN: Auxiliary script that builds the flags file (from mapping) and

    runs the LEXLOG smoke evaluation (Art. 286).

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

import os
import subprocess
import sys

FLAGS_PATH = os.path.join("packs", "jurisdictions", "PL", "flags", "lexenith_results_latest.json")


def main():
    print("[INFO] Building flags from mapping for R_286_OSZUSTWO...")

    subprocess.run(
        [
            sys.executable,
            "scripts/build_flags_from_mapping.py",
            "--rule-id",
            "R_286_OSZUSTWO",
        ],
        check=True,
    )

    print("[INFO] Running smoke with generated flags...")

    subprocess.run(
        [sys.executable, "scripts/lexlog_eval_smoke.py", "--flags", FLAGS_PATH],
        check=True,
    )


if __name__ == "__main__":
    main()
