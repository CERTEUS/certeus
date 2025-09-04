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
import logging
import os
import time

from fastapi import FastAPI, Request, Response

from core.pco.crypto import b64u_decode, load_pubkey_bytes_from_env

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

__all__ = ["attach_proof_only_middleware"]


def attach_proof_only_middleware(app: FastAPI) -> None:
    # 1) Proof-only (optional)

    if os.getenv("STRICT_PROOF_ONLY") == "1":
        logger = logging.getLogger("proofgate")

        def _is_protected(path: str, method: str) -> bool:
            # Publish-like and mutating endpoints which require a PCO token
            protected_exact = {
                "/v1/pco/bundle",
                "/v1/proofgate/publish",
                "/v1/export",
            }
            if path in protected_exact and method.upper() == "POST":
                return True
            return False

        def _extract_token(req: Request) -> str | None:
            # Prefer Authorization: Bearer <JWS>, fallback to X-PCO-Token
            auth = req.headers.get("authorization") or req.headers.get("Authorization")
            if auth and auth.lower().startswith("bearer "):
                return auth.split(" ", 1)[1].strip()
            x = req.headers.get("x-pco-token") or req.headers.get("X-PCO-Token")
            return x.strip() if x else None

        def _verify_ed25519_jws(jws: str) -> bool:
            try:
                parts = jws.split(".")
                if len(parts) != 3:
                    return False
                header_b64u, payload_b64u, sig_b64u = parts
                signing_input = (header_b64u + "." + payload_b64u).encode("ascii")
                header = b64u_decode(header_b64u)
                # minimal header check (alg EdDSA)
                if b'"EdDSA"' not in header and b'EdDSA' not in header:
                    return False
                pk = load_pubkey_bytes_from_env()
                from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

                Ed25519PublicKey.from_public_bytes(pk).verify(b64u_decode(sig_b64u), signing_input)
                return True
            except Exception:
                return False

        @app.middleware("http")
        async def _proof_only(  # type: ignore[override]
            request: Request, call_next: Callable[[Request], Response]
        ) -> Response:
            try:
                path = request.url.path
                method = request.method
                if _is_protected(path, method):
                    tok = _extract_token(request)
                    if not tok or not _verify_ed25519_jws(tok):
                        try:
                            logger.warning("DROP: missing/invalid PCO token path=%s method=%s", path, method)
                        except Exception:
                            pass
                        return Response(status_code=403, content="DROP: proof-required")
            except Exception:
                # Safety net: do not block traffic unless clearly invalid
                pass
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
        _rl_paths = {p.strip() for p in (os.getenv("RATE_LIMIT_PATHS") or "/health").split(",") if p.strip()}

        @app.middleware("http")
        async def _rate_limit(  # type: ignore[override]
            request: Request, call_next: Callable[[Request], Response]
        ) -> Response:
            try:
                # Ogranicz RL do wybranych ścieżek (np. /health)
                path = request.url.path
                if path not in _rl_paths:
                    return await call_next(request)

                ip = request.client.host if request.client else "unknown"
                key = f"{ip}::{path}"

                now = time.time()
                win, cnt = _rl_state.get(key, (now, 0))
                if now - win >= 60.0:
                    win, cnt = now, 0
                cnt += 1
                _rl_state[key] = (win, cnt)
                if cnt > rl_per_min:
                    return Response(status_code=429, content="Too Many Requests")
            except Exception:
                pass
            return await call_next(request)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
