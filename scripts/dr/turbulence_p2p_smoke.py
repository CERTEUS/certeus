#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/dr/turbulence_p2p_smoke.py                   |
# | ROLE: Smoke: P2P turbulence (simulated load)                 |
# | PLIK: scripts/dr/turbulence_p2p_smoke.py                   |
# | ROLA: Smoke: turbulencje P2P (symulowany load)               |
# +-------------------------------------------------------------+

"""
PL: Symulacja turbulencji P2P: wysyła serię żądań GET/POST do kilku endpointów
    i raportuje p95 oraz error_rate. Report‑only; zapisuje `out/turbulence_p2p.json`.

EN: P2P turbulence simulation: sends a series of GET/POST requests to a few
    endpoints and reports p95 and error_rate. Report‑only; writes `out/turbulence_p2p.json`.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import json
from pathlib import Path
import random
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


def run_turbulence(iters: int = 30) -> tuple[dict[str, Any], float, float]:
    c = TestClient(app)
    durs: list[float] = []
    errors = 0
    endpoints = [
        ("GET", "/v1/lexqft/coverage", None),
        ("POST", "/v1/devices/horizon_drive/plan", {"target_horizon": 0.2}),
        ("POST", "/v1/qtm/measure", {"operator": "L", "source": "P2P"}),
    ]
    for _ in range(max(1, iters)):
        method, path, body = random.choice(endpoints)
        t0 = time.perf_counter()
        try:
            if method == "GET":
                r = c.get(path)
            else:
                r = c.post(path, json=body)
            ok = 200 <= r.status_code < 500  # count 5xx as error
        except Exception:
            ok = False
        durs.append((time.perf_counter() - t0) * 1000.0)
        if not ok:
            errors += 1
    p95 = _p95(durs)
    erate = errors / max(1, len(durs))
    return (
        {"count": len(durs), "p95_ms": round(p95, 2), "error_rate": round(erate, 4)},
        p95,
        erate,
    )


def main() -> int:  # pragma: no cover (integration)
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=30)
    ap.add_argument("--out", default="out/turbulence_p2p.json")
    ap.add_argument("--p95-max-ms", type=float, default=500.0)
    ap.add_argument("--max-error-rate", type=float, default=0.05)
    args = ap.parse_args()

    report, p95, er = run_turbulence(args.iters)
    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(report, indent=2), encoding="utf-8")

    ok = (p95 <= args.p95_max_ms) and (er <= args.max_error_rate)
    status = "OK" if ok else "WARN"
    print(
        f"P2P turbulence: p95={p95:.2f} ms (<= {args.p95_max_ms}), er={er:.4f} (<= {args.max_error_rate}) => {status}"
    )
    # report-only: return 0 always in CI; use env to enforce if needed later
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
