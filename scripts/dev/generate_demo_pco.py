#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/dev/generate_demo_pco.py                    |
# | ROLE: Project script.                                       |
# | PLIK: scripts/dev/generate_demo_pco.py                    |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: Generator przykładowego publicznego PCO do folderu `data/public_pco/shard-0/`.
    Tworzy spójny wpis (rid/smt2_hash/lfsc/ledger.merkle_root) zgodny z bulk_reconstruct().

EN: Generates a demo public PCO into `data/public_pco/shard-0/` that is consistent
    with bulk_reconstruct() (rid/smt2_hash/lfsc/ledger.merkle_root).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import sys

# === KONFIGURACJA / CONFIGURATION ===

# === LOGIKA / LOGIC ===


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    # Ensure repo root on sys.path for local imports
    sys.path.insert(0, str(repo))
    out_dir = repo / "data" / "public_pco" / "shard-0"
    out_dir.mkdir(parents=True, exist_ok=True)

    rid = "RID-DEMO-1"
    smt2 = "(set-logic ALL) (check-sat)\n".strip()
    smt2_hash = sha256(smt2.encode("utf-8")).hexdigest()
    lfsc = "(lfsc proof)"
    drat = None

    # Compute canonical bundle digest and merkle leaf/root
    from core.pco.crypto import canonical_bundle_hash_hex, compute_leaf_hex

    bundle_hash = canonical_bundle_hash_hex(smt2_hash, lfsc, drat)
    leaf_hex = compute_leaf_hex(rid, bundle_hash)

    obj = {
        "rid": rid,
        "smt2_hash": smt2_hash,
        "lfsc": lfsc,
        "merkle_proof": [],  # empty path -> merkle_root == leaf_hex
        "ledger": {"merkle_root": leaf_hex},
        # Optional fields (for public explorers)
        "signature": "",  # left empty in demo
        "issued_at": "",
    }

    out_path = out_dir / f"{rid}.json"
    out_path.write_text(json.dumps(obj, ensure_ascii=False, indent=2), encoding="utf-8")
    print(str(out_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
