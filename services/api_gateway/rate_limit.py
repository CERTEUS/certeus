#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/rate_limit.py                    |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/rate_limit.py                    |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Lekki middleware token-bucket per-tenant (RATE_LIMIT_QPS opcjonalne).
EN: Lightweight per-tenant token-bucket middleware (optional RATE_LIMIT_QPS).
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===

import os
import time

from fastapi import FastAPI, Request
from fastapi.responses import JSONResponse

# === LOGIKA / LOGIC ===

def attach_rate_limit_middleware(app: FastAPI) -> None:
    qps_env = (os.getenv("RATE_LIMIT_QPS") or "").strip()
    if not qps_env:
        return  # disabled by default
    try:
        rate_qps = float(qps_env)
    except Exception:
        return
    burst = float(os.getenv("RATE_LIMIT_BURST") or 10)

    # state: tenant -> (tokens, last_ts)
    buckets: dict[str, tuple[float, float]] = {}

    @app.middleware("http")
    async def _rate_limiter(request: Request, call_next):  # type: ignore
        try:
            tenant = request.headers.get("X-Tenant-ID") or request.headers.get("X-Org-ID") or "anonymous"
            now = time.monotonic()
            tokens, last = buckets.get(tenant, (burst, now))
            # refill
            tokens = min(burst, tokens + (now - last) * rate_qps)
            if tokens < 1.0:
                return JSONResponse({"detail": "Rate limit exceeded"}, status_code=429)
            tokens -= 1.0
            buckets[tenant] = (tokens, now)
        except Exception:
            pass
        return await call_next(request)

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
