#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/tenant_slo_trend_gate.py            |
# | ROLE: SLO trend gate (per-tenant)                             |
# | PLIK: scripts/slo_gate/tenant_slo_trend_gate.py            |
# | ROLA: Bramka trendu SLO (per-tenant)                          |
# +-------------------------------------------------------------+

"""
PL: Bramka trendu SLO per-tenant — porównuje `out/tenant_slo.json` z
    `out/prev_tenant_slo.json` i raportuje wzrost p95 > próg (domyślnie 10%).
    Report‑only (zwraca 0).

EN: Per-tenant SLO trend gate — compares `out/tenant_slo.json` with
    `out/prev_tenant_slo.json` and reports p95 increases above threshold
    (default 10%). Report‑only (returns 0).
"""

from __future__ import annotations

import json
import os
from pathlib import Path

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def _read_json(p: Path) -> dict:
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {}


def main() -> int:  # pragma: no cover
    repo = Path(".").resolve()
    cur_p = repo / "out" / "tenant_slo.json"
    prev_p = repo / "out" / "prev_tenant_slo.json"
    thr_pct = float(os.getenv("TENANT_SLO_ALLOW_PCT", "10")) / 100.0
    if not cur_p.exists() or not prev_p.exists():
        print("Tenant SLO trend: not enough data (skipping)")
        return 0
    cur = _read_json(cur_p)
    prev = _read_json(prev_p)
    violations = []
    for tenant, stats in (cur or {}).items():
        try:
            c_p95 = float(stats.get("p95_ms", 0.0))
            p_p95 = float((prev.get(tenant) or {}).get("p95_ms", 0.0))
        except Exception:
            continue
        if p_p95 > 0 and c_p95 > p_p95 * (1.0 + thr_pct):
            violations.append((tenant, p_p95, c_p95))
    if violations:
        print("Tenant SLO trend: VIOLATIONS (report-only)")
        for t, p, c in violations:
            print(
                f" - {t}: p95 {c:.2f} ms > allowed {(p * (1.0 + thr_pct)):.2f} ms (base {p:.2f})"
            )
    else:
        print("Tenant SLO trend: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
