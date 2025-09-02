#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/slo_gate/measure_api.py                     |
# | ROLE: Project script.                                       |
# | PLIK: scripts/slo_gate/measure_api.py                     |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Pomiar SLO API w trybie DEV bez serwera (ASGI in‑proc). Zapisuje `out/slo.json`
    z metrykami p95 i error_rate.

EN: Measure API SLO in DEV without a live server (in‑proc ASGI). Writes
    `out/slo.json` with p95 and error_rate.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path
import statistics
import sys
import time

from fastapi.testclient import TestClient

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from services.api_gateway.main import app  # noqa: E402

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===


# === LOGIKA / LOGIC ===


def _measure(client: TestClient, *, n: int) -> tuple[list[float], int]:
    lat_ms: list[float] = []
    errors = 0
    urls = ["/docs", "/openapi.json"]
    for i in range(n):
        url = urls[i % len(urls)]
        t0 = time.perf_counter()
        r = client.get(url)
        lat_ms.append((time.perf_counter() - t0) * 1000.0)
        if r.status_code >= 400:
            errors += 1
    return lat_ms, errors


def main() -> int:
    count = int(os.getenv("SLO_MEASURE_COUNT", "60") or "60")
    out_path = Path(os.getenv("SLO_OUT", "out/slo.json"))
    out_path.parent.mkdir(parents=True, exist_ok=True)

    with TestClient(app) as client:
        lat_ms, errors = _measure(client, n=count)

    p95 = statistics.quantiles(lat_ms, n=100)[94] if lat_ms else 0.0
    error_rate = errors / max(1, len(lat_ms))

    payload = {"p95_ms": p95, "error_rate": error_rate, "count": len(lat_ms), "observed_at": time.time()}
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps(payload))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
