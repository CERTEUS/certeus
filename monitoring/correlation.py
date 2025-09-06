#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: monitoring/correlation.py                             |
# | ROLE: Correlation/trace linkage middleware                   |
# | PLIK: monitoring/correlation.py                             |
# | ROLA: Middleware korelacji/wiązania trace                   |
# +-------------------------------------------------------------+

"""
PL: Middleware dodający i propagujący `X-Correlation-ID` oraz – jeśli dostępne –
    identyfikatory `trace_id/span_id` z OpenTelemetry. Ustawia też nagłówki PCO
    (prefiks `X-CERTEUS-PCO-correlation.*`) tak, aby każda odpowiedź miała
    spójny most: trace ↔ correlation_id ↔ PCO.

EN: Middleware that adds and propagates `X-Correlation-ID` and, if available,
    OpenTelemetry `trace_id/span_id`. It also sets PCO headers
    (`X-CERTEUS-PCO-correlation.*`) so each response exposes a consistent bridge:
    trace ↔ correlation_id ↔ PCO.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
import typing as _t
import uuid

from fastapi import FastAPI, Request, Response

import logging
from monitoring.otel_setup import set_span_attrs

# === LOGIKA / LOGIC ===

__all__ = ["attach_correlation_middleware", "get_current_trace_ids"]


def _norm_uuid(value: str | None) -> str:
    try:
        if value:
            # accept raw uuid or any non-empty string; normalize to UUIDv4 if parsable
            return str(uuid.UUID(value))
    except Exception as exc:
        logging.getLogger(__name__).debug("_norm_uuid parse failed (%s): %s", value, exc)
    return str(uuid.uuid4())


def get_current_trace_ids() -> tuple[str | None, str | None]:
    """
    PL: Pobiera (trace_id, span_id) jako heksy (lowercase) jeśli OTel jest aktywny.
    EN: Returns (trace_id, span_id) as lowercase hex if OTel is active.
    """
    try:  # lazy import; optional dependency
        from opentelemetry import trace  # type: ignore

        span = trace.get_current_span()
        ctx = span.get_span_context()
        if not getattr(ctx, "is_valid", lambda: False)():
            return (None, None)
        trace_hex = f"{ctx.trace_id:032x}"
        span_hex = f"{ctx.span_id:016x}"
        return (trace_hex, span_hex)
    except Exception as exc:
        logging.getLogger(__name__).debug("get_current_trace_ids failed: %s", exc)
        return (None, None)


def attach_correlation_middleware(app: FastAPI) -> None:
    """
    PL: Wstrzykuje middleware korelacji do aplikacji FastAPI.
    EN: Attaches correlation middleware to the FastAPI app.
    """

    header_in = os.getenv("CORRELATION_HEADER_IN", "X-Correlation-ID")
    header_out = os.getenv("CORRELATION_HEADER_OUT", "X-Correlation-ID")

    # Try to load RA fingerprint once (TEE profile)
    _ra_fp: str | None = None
    try:
        ra_env = os.getenv("TEE_RA_FINGERPRINT")
        if ra_env:
            _ra_fp = ra_env.strip()
        else:
            from pathlib import Path as _P  # local import

            p = _P("infra/tee/attestation.json")
            if p.exists():
                import json as _json

                js = _json.loads(p.read_text(encoding="utf-8"))
                val = js.get("measurement") or js.get("mrenclave") or js.get("fingerprint") or ""
                _ra_fp = str(val).strip() or None
    except Exception as exc:
        logging.getLogger(__name__).debug("attach_correlation_middleware RA load failed: %s", exc)
        _ra_fp = None

    @app.middleware("http")
    async def _correlation(  # type: ignore[override]
        request: Request, call_next: _t.Callable[[Request], Response]
    ) -> Response:
        # 1) Extract/generate correlation ID
        corr = request.headers.get(header_in) or request.headers.get(header_in.lower())
        corr_id = _norm_uuid(corr)

        # 2) Make it available for handlers
        try:
            request.state.correlation_id = corr_id  # type: ignore[attr-defined]
        except Exception as exc:
            logging.getLogger(__name__).debug("set request.state.correlation_id failed: %s", exc)

        # 3) Set OTel span attributes if tracer is present
        try:
            set_span_attrs({"correlation_id": corr_id})
        except Exception as exc:
            logging.getLogger(__name__).debug("set_span_attrs(correlation_id) failed: %s", exc)

        # 4) Process the request
        response = await call_next(request)

        # 5) Add response headers for correlation + PCO bridge
        try:
            response.headers[header_out] = corr_id
        except Exception as exc:
            logging.getLogger(__name__).debug("set response header %s failed: %s", header_out, exc)

        trace_id, span_id = get_current_trace_ids()
        try:
            if trace_id:
                response.headers.setdefault("X-Trace-Id", trace_id)
                set_span_attrs({"trace_id": trace_id})
            if span_id:
                response.headers.setdefault("X-Span-Id", span_id)
                set_span_attrs({"span_id": span_id})
        except Exception as exc:
            logging.getLogger(__name__).debug("set trace/span headers failed: %s", exc)

        # PCO correlation headers (public, safe)
        try:
            response.headers.setdefault("X-CERTEUS-PCO-correlation.correlation_id", corr_id)
            if trace_id:
                response.headers.setdefault("X-CERTEUS-PCO-correlation.trace_id", trace_id)
        except Exception as exc:
            logging.getLogger(__name__).debug("set PCO correlation headers failed: %s", exc)

        # Optional: advertise TEE RA fingerprint (if provided), to be bound into PCO
        try:
            if _ra_fp:
                response.headers.setdefault("X-CERTEUS-PCO-tee.ra.fingerprint", _ra_fp)
        except Exception as exc:
            logging.getLogger(__name__).debug("set RA fingerprint header failed: %s", exc)

        return response


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
