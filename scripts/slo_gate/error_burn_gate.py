#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/error_burn_gate.py                 |
# | ROLE: SLO burn-rate gate (report-only)                       |
# | PLIK: scripts/slo_gate/error_burn_gate.py                 |
# | ROLA: Bramka SLO burn-rate (raport)                          |
# +-------------------------------------------------------------+

"""
PL: Bramka burn-rate SLO — czyta `out/endpoint_slo.json` i raportuje, jeśli
    error_rate przekracza zadany próg (domyślnie 5%). Report‑only; exit 0.

EN: SLO burn-rate gate — reads `out/endpoint_slo.json` and reports when
    error_rate exceeds threshold (default 5%). Report‑only; exit 0.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===
import json
import os
from pathlib import Path

# === LOGIKA / LOGIC ===


def main() -> int:  # pragma: no cover
    repo = Path(".").resolve()
    p = repo / "out" / "endpoint_slo.json"
    thr = float(os.getenv("ENDPOINT_MAX_ERROR_RATE", "0.05"))
    if not p.exists():
        print("Burn-rate: no endpoint_slo.json; skip")
        return 0
    try:
        data: dict[str, dict[str, float]] = json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        print("Burn-rate: invalid endpoint_slo.json; skip")
        return 0
    violations = []
    for key, stats in (data or {}).items():
        try:
            er = float(stats.get("error_rate", 0.0))
        except Exception:
            continue
        if er > thr:
            violations.append((key, er))
    if violations:
        print("Burn-rate: VIOLATIONS (report-only)")
        for k, er in violations:
            print(f" - {k}: error_rate={er:.4f} > {thr}")
    else:
        print("Burn-rate: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
