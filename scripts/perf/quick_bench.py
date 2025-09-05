#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/perf/quick_bench.py                          |
# | ROLE: Quick in-proc perf bench (p95)                         |
# | PLIK: scripts/perf/quick_bench.py                          |
# | ROLA: Szybki benchmark in-proc (p95)                        |
# +-------------------------------------------------------------+

"""
PL: Szybki benchmark (TestClient) — mierzy czasy odpowiedzi dla kilku
    endpointów i raportuje p95. Opcjonalnie sprawdza próg.

EN: Quick perf bench (TestClient) — times a few endpoints and reports p95.
    Optionally enforces a threshold.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
from pathlib import Path
import statistics
import sys
import time
from typing import Any

from fastapi.testclient import TestClient

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from services.api_gateway.main import app  # noqa: E402

# === LOGIKA / LOGIC ===

ENDPOINTS = [
    ("GET", "/health"),
    ("GET", "/openapi.json"),
    ("GET", "/metrics"),
]


def _time_endpoint(client: TestClient, method: str, path: str, n: int) -> list[float]:
    durs: list[float] = []
    for _ in range(n):
        t0 = time.perf_counter()
        if method == "GET":
            r = client.get(path)
        else:
            r = client.request(method, path)
        r.raise_for_status()
        durs.append((time.perf_counter() - t0) * 1000.0)
    return durs


def _warm_up(client: TestClient, rounds: int = 3) -> None:
    """PL/EN: Rozgrzewka: pierwsze wywołania mogą budować cache/struktury.

    Warm up endpoints to avoid counting cold-start costs in measurements.
    """
    for _ in range(max(0, rounds)):
        for method, path in ENDPOINTS:
            if method == "GET":
                try:
                    client.get(path)
                except Exception:
                    pass
            else:
                try:
                    client.request(method, path)
                except Exception:
                    pass


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=10)
    ap.add_argument("--p95-max-ms", type=float, default=250.0)
    ap.add_argument("--out", default="out/perf_bench.json")
    args = ap.parse_args()

    client = TestClient(app)
    # Warm-up to stabilize p95 (cache OpenAPI, import paths, etc.)
    _warm_up(client, rounds=3)
    worst_p95 = 0.0
    results: dict[str, Any] = {"endpoints": [], "iters": args.iters}
    for method, path in ENDPOINTS:
        durs = _time_endpoint(client, method, path, args.iters)
        p95 = statistics.quantiles(durs, n=100)[94]
        worst_p95 = max(worst_p95, p95)
        results["endpoints"].append(
            {
                "method": method,
                "path": path,
                "p95_ms": p95,
                "min_ms": min(durs),
                "max_ms": max(durs),
            }
        )
        print(f"{method} {path}: p95={p95:.2f} ms over {args.iters} iters")

    # write JSON report
    import json
    import os

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    results["worst_p95_ms"] = worst_p95
    results["threshold_ms"] = args.p95_max_ms
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(results, fh, indent=2)

    if worst_p95 > args.p95_max_ms:
        print(f"Perf bench: FAIL worst p95={worst_p95:.2f} ms > {args.p95_max_ms} ms")
        return 1
    print(f"Perf bench: OK worst p95={worst_p95:.2f} ms <= {args.p95_max_ms} ms")
    return 0


# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
