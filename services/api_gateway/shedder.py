#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/shedder.py                      |
# | ROLE: Adaptive shedder middleware (env-controlled)          |
# | PLIK: services/api_gateway/shedder.py                      |
# | ROLA: Middleware adaptacyjnego sheddera (ster. ENV)         |
# +-------------------------------------------------------------+
"""
PL: Prosty shedder adaptacyjny sterowany ENV:
    - SHED_ENABLE=1 włącza middleware,
    - SHED_FORCE_RATE in [0,1] – prawdop. odrzucenia ciężkich żądań,
    - SHED_MAX_RATE in [0,1] – górne ograniczenie (domyślnie 1).

EN: Simple adaptive shedder controlled via ENV.
"""

from __future__ import annotations

from collections.abc import Callable
import os
import random

from fastapi import FastAPI, Request
from fastapi.responses import JSONResponse


def _env_flag(name: str) -> bool:
    return (os.getenv(name) or "").strip() in {"1", "true", "True"}


def _env_float(name: str, default: float) -> float:
    try:
        return float(os.getenv(name) or default)
    except Exception:
        return default


def _is_heavy_endpoint(path: str, method: str) -> bool:
    p = path or ""
    return p.startswith("/v1/qtm/measure") and method.upper() == "POST"


def attach_shedder_middleware(app: FastAPI) -> None:
    @app.middleware("http")
    async def _shedder(request: Request, call_next: Callable):  # type: ignore
        try:
            if _env_flag("SHED_ENABLE") and _is_heavy_endpoint(request.url.path, request.method):
                force_rate = max(0.0, min(1.0, _env_float("SHED_FORCE_RATE", 0.0)))
                max_rate = max(0.0, min(1.0, _env_float("SHED_MAX_RATE", 1.0)))
                rate = min(force_rate, max_rate)
                if rate > 0.0 and random.random() < rate:
                    return JSONResponse({"detail": "shed"}, status_code=503)
        except Exception:
            pass
        return await call_next(request)
