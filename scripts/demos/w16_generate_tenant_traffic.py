#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/w16_generate_tenant_traffic.py         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/w16_generate_tenant_traffic.py         |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Demo W16 — generuje ruch per‑tenant do API (FIN/LEX/system), aby zasilić
    metryki per‑tenant (p95/error‑rate). Skrypt jest idempotentny i prosty.

EN: W16 demo — generates per‑tenant traffic against the API (FIN/LEX/system)
    to feed per‑tenant metrics (p95/error‑rate). Idempotent and simple.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from collections.abc import Iterable
import os
import random
import time

import requests

# === KONFIGURACJA / CONFIGURATION ===

BASE = os.getenv("CERTEUS_BASE", "http://127.0.0.1:8000").rstrip("/")
TENANTS: list[str] = ["acme", "globex", "initech"]
N_REQ: int = int(os.getenv("N_REQ", "20"))
SLEEP_S: float = float(os.getenv("SLEEP_S", "0.05"))


# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def _do(method: str, path: str, *, tenant: str, json: dict | None = None, files: dict | None = None) -> int:
    url = f"{BASE}{path}"
    headers = {"X-Tenant-ID": tenant}
    try:
        if method == "GET":
            r = requests.get(url, headers=headers, timeout=10)
        elif method == "POST":
            r = requests.post(url, headers=headers, json=json, files=files, timeout=15)
        else:
            raise ValueError(method)
        return r.status_code
    except Exception:
        return 599  # synthetic error


def _drive_fin(tenant: str) -> None:
    _do(
        "POST",
        "/v1/fin/alpha/simulate",
        tenant=tenant,
        json={"strategy_id": random.choice(["qalpha-momentum", "qalpha-arb"]), "capital": 100_000, "horizon_days": 30},
    )
    _do("GET", "/v1/fin/alpha/pnl", tenant=tenant)


def _drive_lex(tenant: str) -> None:
    _do("GET", "/v1/lexenith/pilot/cases", tenant=tenant)
    _do(
        "POST",
        "/v1/lexenith/pilot/feedback",
        tenant=tenant,
        json={"case_id": "LEX-PILOT-001", "rating": random.choice([4, 5])},
    )


def _drive_system(tenant: str) -> None:
    _do("GET", "/metrics", tenant=tenant)


def main() -> int:
    rnd = random.Random(42)
    tenants: Iterable[str] = [rnd.choice(TENANTS) for _ in range(N_REQ)]
    oks = errs = 0
    for t in tenants:
        for driver in (_drive_fin, _drive_lex, _drive_system):
            try:
                driver(t)
                oks += 1
            except Exception:
                errs += 1
            time.sleep(SLEEP_S)
    print(f"Done. OK={oks} ERR={errs} base={BASE}")
    return 0


# === I/O / ENDPOINTS ===


if __name__ == "__main__":
    raise SystemExit(main())

# === TESTY / TESTS ===
