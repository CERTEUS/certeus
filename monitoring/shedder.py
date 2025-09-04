#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: monitoring/shedder.py                                 |
# | ROLE: Adaptive load shedding (QTMP-aware)                    |
# | PLIK: monitoring/shedder.py                                 |
# | ROLA: Adaptacyjny load‑shedding (QTMP-aware)                 |
# +-------------------------------------------------------------+

"""
PL: Adaptacyjny shedder ruchu HTTP sterowany p95 oraz sygnałami QTMP.
    Główne założenia:
      - Target p95 (ms) — gdy przekroczony, zwiększamy odsetek shedowania.
      - Bias QTMP — wysoka latencja collapse/próg L_T podbijają shed‑rate.
      - Najpierw shed dla obciążeń ciężkich (POST /v1/qtm, /v1/cfe itp.).

EN: Adaptive HTTP traffic shedder driven by p95 and QTMP signals.
    Principles:
      - Target p95 (ms); above target increases shed rate.
      - QTMP bias; high collapse latency / UB L_T increase shed rate.
      - Prefer shedding heavy endpoints first (e.g., POST /v1/qtm, /v1/cfe).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import os
import random
import typing as _t

from fastapi import FastAPI, Request, Response

from monitoring.metrics_slo import certeus_http_shed_total

# === LOGIKA / LOGIC ===

_STATE: dict[str, float] = {
    "qtmp_last_latency_ms": 0.0,
    "qtmp_last_ub_lt": 0.0,
}


def update_from_qtmp(ub_lt: float | None = None, collapse_latency_ms: float | None = None) -> None:
    if ub_lt is not None:
        try:
            _STATE["qtmp_last_ub_lt"] = float(ub_lt)
        except Exception:
            pass
    if collapse_latency_ms is not None:
        try:
            _STATE["qtmp_last_latency_ms"] = float(collapse_latency_ms)
        except Exception:
            pass


def _current_worst_p95_ms() -> float:
    try:
        from monitoring.metrics_slo import http_series

        series = http_series(10).get("series", [])  # type: ignore[assignment]
        worst = 0.0
        for s in series:  # type: ignore[assignment]
            try:
                p95 = float(s.get("p95", 0.0))  # type: ignore[assignment]
            except Exception:
                p95 = 0.0
            if p95 > worst:
                worst = p95
        return worst
    except Exception:
        return 0.0


def _compute_shed_rate() -> float:
    # Env config
    target = float(os.getenv("SHED_TARGET_P95_MS", "250") or 250.0)
    max_rate = float(os.getenv("SHED_MAX_RATE", "0.5") or 0.5)
    base = 0.0
    p95 = _current_worst_p95_ms()
    if p95 > target:
        # linear ramp, capped
        base = min(max_rate, (p95 - target) / max(target, 1.0))
    # QTMP bias
    ub = _STATE.get("qtmp_last_ub_lt", 0.0)
    lat = _STATE.get("qtmp_last_latency_ms", 0.0)
    bias = 0.0
    if ub >= 0.35:
        bias += 0.1
    if lat >= 200.0:
        bias += 0.1
    rate = min(max_rate, max(0.0, base + bias))
    return rate


def _is_sheddable(path: str, method: str) -> bool:
    path = str(path)
    m = method.upper()
    if path.startswith("/metrics") or path.startswith("/v1/metrics"):
        return False
    if path in {"/health", "/openapi.json"}:
        return False
    # Focus on heavy/compute or mutating endpoints
    if m != "GET":
        return True
    if path.startswith("/v1/qtm") or path.startswith("/v1/cfe") or path.startswith("/v1/lexqft"):
        return True
    return False


def attach_shedder_middleware(app: FastAPI) -> None:
    if (os.getenv("SHED_ENABLE") or "").strip() not in {"1", "true", "True"}:
        return

    @app.middleware("http")
    async def _shedder(request: Request, call_next: _t.Callable[[Request], Response]) -> Response:  # type: ignore[override]
        try:
            path = request.url.path
            method = request.method
            if _is_sheddable(path, method):
                rate = _compute_shed_rate()
                if rate > 0.0 and random.random() < rate:
                    tenant = "anonymous"
                    try:
                        from services.api_gateway.limits import get_tenant_id

                        tenant = get_tenant_id(request)
                    except Exception:
                        pass
                    certeus_http_shed_total.labels(tenant=tenant, path=path, method=method, reason="adaptive").inc()
                    return Response(status_code=503, content="Service Busy (shed)", headers={"Retry-After": "0"})
        except Exception:
            # Safety net: never block traffic due to shedder errors
            pass
        return await call_next(request)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
