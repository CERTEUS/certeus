#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/endpoint_slo_sanity.py             |
# | ROLE: SLO smoke per-endpoint (report-only)                   |
# | PLIK: scripts/slo_gate/endpoint_slo_sanity.py             |
# | ROLA: SLO smoke per-endpoint (raport)                        |
# +-------------------------------------------------------------+

"""
PL: SLO smoke per-endpoint — mierzy p95 i error_rate dla wybranych endpointów
    (GET/POST z minimalnym payloadem). Report‑only; zapisuje `out/endpoint_slo.json`.

EN: Per-endpoint SLO smoke — measures p95 and error_rate for selected endpoints
    (GET/POST with minimal payload). Report‑only; writes `out/endpoint_slo.json`.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===
import argparse
import json
from pathlib import Path
import time
from typing import Any

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === LOGIKA / LOGIC ===


def _p95(vals: list[float]) -> float:
    if not vals:
        return 0.0
    s = sorted(vals)
    k = max(0, min(len(s) - 1, int(0.95 * (len(s) - 1))))
    return s[k]


def _call(c: TestClient, method: str, path: str, body: dict[str, Any] | None) -> tuple[float, bool]:
    t0 = time.perf_counter()
    try:
        if method == "GET":
            r = c.get(path)
        else:
            r = c.post(path, json=body or {})
        ok = 200 <= r.status_code < 500
    except Exception:
        ok = False
    return (time.perf_counter() - t0) * 1000.0, ok


def main() -> int:  # pragma: no cover (integration)
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=10)
    ap.add_argument("--out", default="out/endpoint_slo.json")
    args = ap.parse_args()

    c = TestClient(app)
    targets: list[tuple[str, str, dict[str, Any] | None]] = [
        ("GET", "/health", None),
        ("GET", "/openapi.json", None),
        ("GET", "/v1/lexqft/coverage", None),
        ("POST", "/v1/devices/horizon_drive/plan", {}),
        ("POST", "/v1/qtm/measure", {"operator": "L", "source": "SLO"}),
    ]

    report: dict[str, dict[str, Any]] = {}
    for method, path, body in targets:
        durs: list[float] = []
        errors = 0
        for _ in range(max(1, args.iters)):
            dur, ok = _call(c, method, path, body)
            durs.append(dur)
            if not ok:
                errors += 1
        report[f"{method} {path}"] = {
            "count": len(durs),
            "p95_ms": round(_p95(durs), 2),
            "error_rate": round(errors / max(1, len(durs)), 4),
        }

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"Endpoint SLO: wrote {outp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
