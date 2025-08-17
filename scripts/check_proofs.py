# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/scripts/check_proofs.py                 |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                        CERTEUS                              |
# |            Proof-Gate: Artifact Integrity Checker           |
# +-------------------------------------------------------------+
# ── CERTEUS Project ─────────────────────────────────────────────────────────────
# File: scripts/check_proofs.py
# License: Apache-2.0
# Description (PL): Weryfikacja SHA256 artefaktów DRAT/LFSC.
# Description (EN): Verifies SHA256 of DRAT/LFSC artifacts.
# Style Guide: PL/EN docs, labeled blocks. (See README)
# ────────────────────────────────────────────────────────────────────────────────

"""
PL: Sprawdza istnienie plików {z3.drat,cvc5.lfsc} i ich plików *.sha256,
    porównuje wyliczone sumy SHA256 z zapisanymi. Zwraca kod 0/1.

EN: Checks presence of {z3.drat,cvc5.lfsc} and their *.sha256 files,
    compares computed SHA256 with recorded ones. Returns code 0/1.
"""

# [BLOCK: IMPORTS / IMPORTY]
from __future__ import annotations
import argparse
import hashlib
import sys
from pathlib import Path

# [BLOCK: CLI]
parser = argparse.ArgumentParser()
parser.add_argument(
    "--dir",
    default="proof-artifacts",
    help="PL: Katalog artefaktów | EN: Artifacts directory",
)
args = parser.parse_args()
d = Path(args.dir)

# [BLOCK: CHECK FILES / SPRAWDŹ PLIKI]
required = ["z3.drat", "z3.drat.sha256", "cvc5.lfsc", "cvc5.lfsc.sha256"]
missing = [name for name in required if not (d / name).exists()]
if missing:
    print(f"ERROR: Missing files: {', '.join(missing)}")
    sys.exit(1)


# [BLOCK: VERIFY / WERYFIKUJ]
def verify(path: Path, sha_path: Path) -> bool:
    recorded = sha_path.read_text(encoding="utf-8").strip().split()[0]
    computed = hashlib.sha256(path.read_bytes()).hexdigest()
    ok = computed == recorded
    print(
        f"{path.name}: {'OK' if ok else 'MISMATCH'} (computed={computed}, recorded={recorded})"
    )
    return ok


ok1 = verify(d / "z3.drat", d / "z3.drat.sha256")
ok2 = verify(d / "cvc5.lfsc", d / "cvc5.lfsc.sha256")

sys.exit(0 if (ok1 and ok2) else 1)
