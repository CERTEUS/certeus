#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/check_slo.py                       |
# | ROLE: Project script.                                       |
# | PLIK: scripts/slo_gate/check_slo.py                       |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Bramka SLO – sprawdza `out/slo.json` względem progów z env:
    - SLO_MAX_P95_MS (domyślnie 300)
    - SLO_MAX_ERROR_RATE (domyślnie 0.01)

EN: SLO gate – checks `out/slo.json` against env thresholds:
    - SLO_MAX_P95_MS (default 300)
    - SLO_MAX_ERROR_RATE (default 0.01)
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path


def main() -> int:
    p = Path(os.getenv("SLO_OUT", "out/slo.json"))
    data = json.loads(p.read_text(encoding="utf-8"))
    max_p95 = float(os.getenv("SLO_MAX_P95_MS", "300"))
    max_err = float(os.getenv("SLO_MAX_ERROR_RATE", "0.01"))
    p95 = float(data.get("p95_ms", 0.0))
    er = float(data.get("error_rate", 0.0))
    ok = (p95 <= max_p95) and (er <= max_err)
    print(
        f"SLO p95={p95:.2f}ms (<= {max_p95}) error_rate={er:.4f} (<= {max_err}) => {'OK' if ok else 'FAIL'}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
