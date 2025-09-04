#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/deploy/canary_progressive_gate.py           |
# | ROLE: Deploy gate script.                                   |
# | PLIK: scripts/deploy/canary_progressive_gate.py           |
# | ROLA: Skrypt bramki wdrożeniowej.                           |
# +-------------------------------------------------------------+

"""
PL: Bramka progresywnego wdrożenia (report‑only). Czyta `deploy/canary_policy.yml`
    i dla każdego etapu uruchamia lekki chaos/turbulence (in‑proc), raportuje
    p95 i error_rate względem progów. Zapisuje `out/canary_report.json`.

EN: Progressive deployment gate (report‑only). Reads `deploy/canary_policy.yml`
    and for each stage runs a lightweight in‑proc turbulence, reporting p95 and
    error_rate against thresholds. Writes `out/canary_report.json`.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===

import json
from pathlib import Path
from typing import Any

try:
    import yaml  # type: ignore
except Exception:  # pragma: no cover
    yaml = None  # type: ignore

from fastapi.testclient import TestClient

from services.api_gateway.main import app


# === LOGIKA / LOGIC ===

def _p95(vals: list[float]) -> float:
    if not vals:
        return 0.0
    s = sorted(vals)
    k = max(0, min(len(s) - 1, int(0.95 * (len(s) - 1))))
    return s[k]


def _exercise(iters: int = 20) -> tuple[float, float]:
    import random
    import time

    c = TestClient(app)
    durs: list[float] = []
    errors = 0
    endpoints = [
        ("GET", "/v1/lexqft/coverage", None),
        ("POST", "/v1/devices/horizon_drive/plan", {"target_horizon": 0.2}),
        ("POST", "/v1/qtm/measure", {"operator": "L", "source": "CANARY"}),
    ]
    for _ in range(max(1, iters)):
        method, path, body = random.choice(endpoints)
        t0 = time.perf_counter()
        try:
            if method == "GET":
                r = c.get(path)
            else:
                r = c.post(path, json=body)
            ok = 200 <= r.status_code < 500
        except Exception:
            ok = False
        durs.append((time.perf_counter() - t0) * 1000.0)
        if not ok:
            errors += 1
    return _p95(durs), errors / max(1, len(durs))


def main() -> int:  # pragma: no cover (integration)
    repo = Path(".").resolve()
    pol = repo / "deploy" / "canary_policy.yml"
    if not pol.exists():
        print("Canary: no policy file found (skip)")
        return 0
    stages: list[dict[str, Any]]
    try:
        if yaml is None:
            raise RuntimeError("yaml not available")
        cfg = yaml.safe_load(pol.read_text(encoding="utf-8")) or {}
        stages = list(cfg.get("stages") or [])
    except Exception:
        print("Canary: invalid policy (skip)")
        return 0

    report: dict[str, Any] = {"stages": []}
    for st in stages:
        p, er = _exercise(20)
        item = {
            "percent": st.get("percent"),
            "p95_ms": round(p, 2),
            "error_rate": round(er, 4),
            "max_p95_ms": st.get("max_p95_ms"),
            "max_error_rate": st.get("max_error_rate"),
        }
        report["stages"].append(item)

    outp = repo / "out" / "canary_report.json"
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print("Canary: report written to", outp)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
