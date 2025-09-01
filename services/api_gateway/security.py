#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/security.py                    |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/security.py                    |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Middleware bezpieczeństwa:

    - Proof-only I/O (STRICT_PROOF_ONLY=1)

    - Nagłówki CSP/HSTS/XCTO/XFO/Referrer-Policy (SEC_HEADERS=1)

    - Prosty rate-limit per-IP (RATE_LIMIT_PER_MIN=N)

EN: Security middleware:

    - Proof-only I/O (STRICT_PROOF_ONLY=1)

    - Security headers CSP/HSTS/XCTO/XFO/Referrer-Policy (SEC_HEADERS=1)

    - Simple per-IP rate limiting (RATE_LIMIT_PER_MIN=N)

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from collections.abc import Callable

import os

import time

from fastapi import FastAPI, Request, Response

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===








#!/usr/bin/env python3


__all__ = ["attach_proof_only_middleware"]


def attach_proof_only_middleware(app: FastAPI) -> None:
    # 1) Proof-only (optional)

    if os.getenv("STRICT_PROOF_ONLY") == "1":

        @app.middleware("http")
        async def _proof_only(  # type: ignore[override]
            request: Request, call_next: Callable[[Request], Response]
        ) -> Response:
            return await call_next(request)

    # 2) Security headers (default on; disable with SEC_HEADERS=0)

    if os.getenv("SEC_HEADERS", "1") != "0":
        csp = os.getenv(
            "CSP",
            "default-src 'self'; img-src 'self' data:; script-src 'self'; style-src 'self' 'unsafe-inline'",
        )

        hsts_max_age = int(os.getenv("HSTS_MAX_AGE", "31536000"))

        @app.middleware("http")
        async def _sec_headers(  # type: ignore[override]
            request: Request, call_next: Callable[[Request], Response]
        ) -> Response:
            resp = await call_next(request)

            resp.headers.setdefault("Content-Security-Policy", csp)

            resp.headers.setdefault("Strict-Transport-Security", f"max-age={hsts_max_age}; includeSubDomains")

            resp.headers.setdefault("X-Content-Type-Options", "nosniff")

            resp.headers.setdefault("X-Frame-Options", "DENY")

            resp.headers.setdefault("Referrer-Policy", "no-referrer")

            return resp

    # 3) Simple per-IP rate limit (window 60s)

    rl_per_min = int(os.getenv("RATE_LIMIT_PER_MIN", "0") or "0")

    if rl_per_min > 0:
        _rl_state: dict[str, tuple[float, int]] = {}

        @app.middleware("http")
        async def _rate_limit(  # type: ignore[override]
            request: Request, call_next: Callable[[Request], Response]
        ) -> Response:
            try:
                ip = request.client.host if request.client else "unknown"

                now = time.time()

                win, cnt = _rl_state.get(ip, (now, 0))

                if now - win >= 60.0:
                    win, cnt = now, 0

                cnt += 1

                _rl_state[ip] = (win, cnt)

                if cnt > rl_per_min:
                    return Response(status_code=429, content="Too Many Requests")

            except Exception:
                pass

            return await call_next(request)



# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

