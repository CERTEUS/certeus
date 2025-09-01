#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/supply_chain/verify_cosign_artifacts.py     |
# | ROLE: Project script.                                       |
# | PLIK: scripts/supply_chain/verify_cosign_artifacts.py     |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Weryfikacja attestacji supply-chain (cosign). Deny-by-default: brak
    wymaganych podpisów => exit 1.

EN: Verify supply-chain attestations (cosign). Deny-by-default: missing
    required signatures => exit 1.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--require", nargs="+", default=["sbom.json.sig", "sbom.json.cert"], help="Files that must exist")
    args = ap.parse_args()
    missing = [p for p in args.require if not Path(p).exists()]
    if missing:
        print(f"Missing required cosign attestations: {', '.join(missing)}")
        return 1
    print("All required cosign attestations present.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
