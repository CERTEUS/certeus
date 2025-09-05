#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/canary_gate.py                        |
# | ROLE: Progressive canary gate (ramp + SLO)                  |
# | PLIK: scripts/gates/canary_gate.py                        |
# | ROLA: Bramka canary/progressive (ramp + SLO)                |
# +-------------------------------------------------------------+

"""
PL: Bramka canary/progressive. W kilku fazach (np. 1%/5%/25%) wykonuje
    pomiar SLO in-proc i weryfikuje progi p95/error-rate. Raport zapisuje
    do `out/canary.json`. Bramka nie zmienia ruchu – to readiness gate.

EN: Canary/progressive gate. Runs in-proc SLO measurements across phases
    (e.g. 1%/5%/25%) and enforces p95/error-rate thresholds. Writes
    `out/canary.json`. This is a readiness gate; it doesn't alter traffic.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import statistics
import sys
import time
from typing import Any

from fastapi.testclient import TestClient

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def _measure(client: TestClient, count: int) -> tuple[float, float, int]:
    import time as _t

    urls = ["/docs", "/openapi.json", "/metrics"]
    lat: list[float] = []
    errs = 0
    for i in range(count):
        url = urls[i % len(urls)]
        t0 = _t.perf_counter()
        r = client.get(url)
        lat.append((_t.perf_counter() - t0) * 1000.0)
        if r.status_code >= 400:
            errs += 1
    p95 = statistics.quantiles(lat, n=100)[94] if lat else 0.0
    er = errs / max(1, len(lat))
    return p95, er, len(lat)


def main() -> int:
    # Ensure repository root in sys.path for local/CI execution
    _repo = Path(__file__).resolve().parents[2]
    if str(_repo) not in sys.path:
        sys.path.insert(0, str(_repo))
    from services.api_gateway.main import app  # lazy import

    ap = argparse.ArgumentParser(description="Canary/progressive readiness gate")
    ap.add_argument("--phases", type=int, default=3, help="Number of phases (e.g. 3 => [1,5,25]%)")
    ap.add_argument("--count", type=int, default=int(os.getenv("CANARY_COUNT", "60") or 60), help="Requests per phase")
    ap.add_argument("--p95-max", type=float, default=float(os.getenv("CANARY_MAX_P95_MS", "250")), help="Max p95 ms")
    ap.add_argument(
        "--error-rate-max", type=float, default=float(os.getenv("CANARY_MAX_ERROR_RATE", "0.01")), help="Max error rate"
    )
    ap.add_argument("--out", default=os.getenv("CANARY_OUT", "out/canary.json"))
    args = ap.parse_args()

    phases_pct = [1, 5, 25, 50, 100][: max(1, args.phases)]
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    results: list[dict[str, Any]] = []
    ok_all = True
    with TestClient(app) as client:
        for pct in phases_pct:
            p95, er, n = _measure(client, args.count)
            ok = (p95 <= args.p95_max) and (er <= args.error_rate_max)
            results.append(
                {
                    "phase_pct": pct,
                    "count": n,
                    "p95_ms": p95,
                    "error_rate": er,
                    "ok": ok,
                }
            )
            if not ok:
                ok_all = False

    payload = {"observed_at": time.time(), "results": results, "ok": ok_all}
    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps(payload))
    return 0 if ok_all else 1


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
