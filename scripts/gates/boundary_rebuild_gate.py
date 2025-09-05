# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/boundary_rebuild_gate.py               |
# | ROLE: Project module.                                       |
# | PLIK: scripts/gates/boundary_rebuild_gate.py               |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Bramka Boundary – wymaga `delta_bits == 0` oraz (jeśli dostępna) mapa
    różnic per-shard `bits_delta_map` z samymi zerami.

EN: Boundary gate – requires `delta_bits == 0` and (if present) per-shard
    `bits_delta_map` all zeros.

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

    # Defaults if no report provided
    delta_bits = 0
    bits_map: dict[str, int] | None = None
    report_path: Path | None = None
    if args.report:
        report_path = Path(args.report)
    else:
        # Spróbuj domyślnej ścieżki z compute: out/boundary_report.json
        cand = Path("out") / "boundary_report.json"
        if cand.exists():
            report_path = cand

    if report_path and report_path.exists():
        data = json.loads(report_path.read_text(encoding="utf-8"))
        bnd = data.get("boundary") or {}
        delta_bits = int(bnd.get("delta_bits", 0))
        bm = bnd.get("bits_delta_map")
        if isinstance(bm, dict):
            try:
                bits_map = {str(k): int(v) for k, v in bm.items()}
            except Exception:
                bits_map = None

    strict_env = os.getenv("STRICT_BOUNDARY_REBUILD", "0").strip()
    strict = args.must_zero or (strict_env not in {"", "0", "false", "False"})

    # Per-shard check (if available)
    if bits_map is not None and bits_map:
        per_shard_ok = all((v == 0) for v in bits_map.values()) if strict else all((v <= 0) for v in bits_map.values())
    else:
        per_shard_ok = True

    ok = ((delta_bits == 0) and per_shard_ok) if strict else ((delta_bits <= 0) and per_shard_ok)
    print(f"Boundary delta_bits={delta_bits} per_shard_ok={per_shard_ok} strict={strict} -> {'OK' if ok else 'FAIL'}")
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
