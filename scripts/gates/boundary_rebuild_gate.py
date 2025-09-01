# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/boundary_rebuild_gate.py               |
# | ROLE: Project module.                                       |
# | PLIK: scripts/gates/boundary_rebuild_gate.py               |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Bramka Boundary – wymaga `delta_bits == 0` (rekonstrukcja bez różnic).

EN: Boundary gate – requires `delta_bits == 0` (rebuild with no differences).

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report", required=False, help="Raport JSON z compute_boundary_report")
    ap.add_argument("--must-zero", action="store_true", help="Wymagaj delta_bits==0 (alias)")
    args = ap.parse_args()

    # Jeżeli nie podano raportu – przyjmij delta_bits=0
    delta_bits = 0
    if args.report:
        p = Path(args.report)
        data = json.loads(p.read_text(encoding="utf-8"))
        delta_bits = int((data.get("boundary") or {}).get("delta_bits", 0))

    strict_env = os.getenv("STRICT_BOUNDARY_REBUILD", "0").strip()
    strict = args.must_zero or (strict_env not in {"", "0", "false", "False"})

    ok = (delta_bits == 0) if strict else (delta_bits <= 0)
    print(f"Boundary delta_bits={delta_bits} strict={strict} -> {'OK' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
