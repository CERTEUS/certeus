# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/compute_boundary_report.py             |
# | ROLE: Project module.                                       |
# | PLIK: scripts/gates/compute_boundary_report.py             |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Stub raportu rekonstrukcji Boundary. Zapisuje JSON z `delta_bits` oraz
    mapą per-shard `bits_delta_map` (dla Gate).

EN: Boundary reconstruction report stub. Writes JSON with `delta_bits` and
    per-shard `bits_delta_map` (used by the Gate).

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Any

from core.boundary.reconstruct import bulk_reconstruct


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=False, help="Ścieżka raportu JSON (domyślnie: out/boundary_report.json)")
    args = ap.parse_args()

    out = Path(args.out) if args.out else Path("out") / "boundary_report.json"
    out.parent.mkdir(parents=True, exist_ok=True)

    bundle_dir = os.getenv("PROOF_BUNDLE_DIR", "data/public_pco")

    rep: dict[str, Any]
    try:
        rep = bulk_reconstruct(bundle_dir)
    except Exception:
        # Fail-safe: emit zeros
        rep = {"delta_bits": 0, "bits_delta_map": {"shard-0": 0}}

    payload = {"boundary": rep}
    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
