#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/endpoint_slo_trend_gate.py         |
# | ROLE: SLO trend gate (per-endpoint)                          |
# | PLIK: scripts/slo_gate/endpoint_slo_trend_gate.py         |
# | ROLA: Bramka trendu SLO (per-endpoint)                       |
# +-------------------------------------------------------------+

"""
PL: Bramka trendu SLO per-endpoint — porównuje `out/endpoint_slo.json` z
    `out/prev_endpoint_slo.json` (z ci-status); raportuje wzrost p95 > próg
    (domyślnie 10%). Report‑only (exit 0).

EN: Per-endpoint SLO trend gate — compares `out/endpoint_slo.json` with
    `out/prev_endpoint_slo.json` (from ci-status); reports p95 increase above
    threshold (default 10%). Report‑only (exit 0).
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===
import json
import os
from pathlib import Path

# === LOGIKA / LOGIC ===


def _read(p: Path) -> dict[str, dict[str, float]]:
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {}


def main() -> int:  # pragma: no cover
    repo = Path(".").resolve()
    cur_p = repo / "out" / "endpoint_slo.json"
    prev_p = repo / "out" / "prev_endpoint_slo.json"
    thr_pct = float(os.getenv("ENDPOINT_SLO_ALLOW_PCT", "10")) / 100.0
    if not cur_p.exists() or not prev_p.exists():
        print("Endpoint SLO trend: not enough data (skip)")
        return 0
    cur = _read(cur_p)
    prev = _read(prev_p)
    violations = []
    for key, stats in (cur or {}).items():
        try:
            c = float(stats.get("p95_ms", 0.0))
            p = float((prev.get(key) or {}).get("p95_ms", 0.0))
        except Exception:
            continue
        if p > 0 and c > p * (1.0 + thr_pct):
            violations.append((key, p, c))
    if violations:
        print("Endpoint SLO trend: VIOLATIONS (report-only)")
        for k, p, c in violations:
            print(
                f" - {k}: p95 {c:.2f} ms > allowed {(p * (1.0 + thr_pct)):.2f} ms (base {p:.2f})"
            )
    else:
        print("Endpoint SLO trend: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
