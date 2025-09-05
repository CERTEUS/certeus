#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/supply_chain_enforce.py                |
# | ROLE: Supply-chain enforcement (optional)                   |
# | PLIK: scripts/gates/supply_chain_enforce.py                |
# | ROLA: Egzekwowanie supply-chain (opcjonalne)                |
# +-------------------------------------------------------------+

"""
PL: Egzekwowanie minimalnych warunków supply-chain:
    - obecność SBOM (`sbom.json`) lub artefaktu `artifact.json`/attestacji.
    - gdy SUPPLY_CHAIN_ENFORCE=1 brak => exit 1, w przeciwnym wypadku INFO.

EN: Enforce minimal supply-chain conditions:
    - presence of SBOM (`sbom.json`) or `artifact.json`/attestation.
    - when SUPPLY_CHAIN_ENFORCE=1 missing => exit 1, otherwise INFO.
"""

from __future__ import annotations

import os
from pathlib import Path

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

def main() -> int:
    enforce = (os.getenv("SUPPLY_CHAIN_ENFORCE") or "0").strip() in {"1", "true", "True"}
    repo = Path(__file__).resolve().parents[2]
    sbom = repo / "sbom.json"
    artifact = repo / "artifact.json"

    ok = sbom.exists() or artifact.exists()
    if ok:
        print("supply-chain: OK (sbom/artifact present)")
        return 0
    if enforce:
        print("supply-chain: FAIL (missing sbom.json/artifact.json)")
        return 1
    print("supply-chain: INFO (no sbom/artifact; enforcement disabled)")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
