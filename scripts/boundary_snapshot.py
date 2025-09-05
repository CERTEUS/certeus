#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/boundary_snapshot.py                        |
# | ROLE: Project script.                                       |
# | PLIK: scripts/boundary_snapshot.py                        |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Tworzy snapshot Boundary do pliku JSON.
EN: Creates Boundary snapshot JSON file.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import os
from pathlib import Path
import sys


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def main() -> int:
    # Ensure repo-root on sys.path for local imports if executed as a script
    sys.path.insert(0, str(_repo_root()))  # noqa: E402
    from core.boundary.snapshot import compute_snapshot, dumps_snapshot  # noqa: E402

    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--dir",
        default=os.getenv("PROOF_BUNDLE_DIR", "data/public_pco"),
        help="Katalog z publicznymi PCO (domyślnie: data/public_pco)",
    )
    ap.add_argument(
        "--out",
        default="out/boundary_snapshot.json",
        help="Ścieżka pliku wyjściowego JSON",
    )
    args = ap.parse_args()

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    snap = compute_snapshot(args.dir)
    out.write_text(dumps_snapshot(snap), encoding="utf-8")
    print(f"Wrote snapshot: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
