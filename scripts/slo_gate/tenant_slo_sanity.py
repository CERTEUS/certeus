#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/tenant_slo_sanity.py               |
# | ROLE: SLO smoke per-tenant (report-only)                     |
# | PLIK: scripts/slo_gate/tenant_slo_sanity.py               |
# | ROLA: SLO smoke per-tenant (raport)                          |
# +-------------------------------------------------------------+

"""
PL: Lekki SLO smoke per tenant — mierzy p95 i error_rate dla kilku endpointów,
    rozdzielnie dla nagłówków `X-Tenant-ID`. Report‑only; zapisuje `out/tenant_slo.json`.

EN: Lightweight per-tenant SLO smoke — measures p95 and error_rate for a few
    endpoints, separately for `X-Tenant-ID` headers. Report‑only; writes
    `out/tenant_slo.json`.
"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

import argparse
import json
from pathlib import Path
import time
from typing import Any

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def _p95(vals: list[float]) -> float:
    if not vals:
        return 0.0
    s = sorted(vals)
    k = max(0, min(len(s) - 1, int(0.95 * (len(s) - 1))))
    return s[k]


def _exercise(c: TestClient, tenant: str, iters: int) -> tuple[float, float, int]:
    durs: list[float] = []
    errors = 0
    headers = {"X-Tenant-ID": tenant}
    for i in range(max(1, iters)):
        # Alternujemy lekki GET i POST (lexqft coverage i qtm measure)
        start = time.perf_counter()
        try:
            if i % 2 == 0:
                r = c.get("/v1/lexqft/coverage", headers=headers)
            else:
                r = c.post(
                    "/v1/qtm/measure",
                    json={"operator": "L", "source": f"TENANT-{tenant}"},
                    headers=headers,
                )
            ok = 200 <= r.status_code < 500
        except Exception:
            ok = False
        durs.append((time.perf_counter() - start) * 1000.0)
        if not ok:
            errors += 1
    return _p95(durs), errors / max(1, len(durs)), len(durs)


def main() -> int:  # pragma: no cover (integration)
    ap = argparse.ArgumentParser()
    ap.add_argument("--tenants", nargs="*", default=["tenant-a", "tenant-b"])
    ap.add_argument("--iters", type=int, default=10)
    ap.add_argument("--out", default="out/tenant_slo.json")
    ap.add_argument("--p95-max-ms", type=float, default=500.0)
    ap.add_argument("--max-error-rate", type=float, default=0.05)
    args = ap.parse_args()

    c = TestClient(app)
    results: dict[str, dict[str, Any]] = {}
    overall_ok = True
    for t in args.tenants:
        p95, er, n = _exercise(c, t, args.iters)
        results[t] = {"count": n, "p95_ms": round(p95, 2), "error_rate": round(er, 4)}
        if p95 > args.p95_max_ms or er > args.max_error_rate:
            overall_ok = False

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(results, indent=2), encoding="utf-8")

    print(
        f"Tenant SLO: {'OK' if overall_ok else 'WARN'} — p95<= {args.p95_max_ms} ms; error_rate<= {args.max_error_rate}"
    )
    # report-only
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
