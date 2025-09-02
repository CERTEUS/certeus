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
import statistics
import time

from fastapi.testclient import TestClient

from services.api_gateway.main import app

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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=10)
    ap.add_argument("--p95-max-ms", type=float, default=250.0)
    args = ap.parse_args()

    client = TestClient(app)
    worst_p95 = 0.0
    for method, path in ENDPOINTS:
        durs = _time_endpoint(client, method, path, args.iters)
        p95 = statistics.quantiles(durs, n=100)[94]
        worst_p95 = max(worst_p95, p95)
        print(f"{method} {path}: p95={p95:.2f} ms over {args.iters} iters")

    if worst_p95 > args.p95_max_ms:
        print(f"Perf bench: FAIL worst p95={worst_p95:.2f} ms > {args.p95_max_ms} ms")
        return 1
    print(f"Perf bench: OK worst p95={worst_p95:.2f} ms <= {args.p95_max_ms} ms")
    return 0


# === I/O / ENDPOINTS ===
if __name__ == "__main__":
    raise SystemExit(main())
