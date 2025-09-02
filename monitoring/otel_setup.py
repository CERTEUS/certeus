#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: monitoring/otel_setup.py                             |
# | ROLE: Optional OpenTelemetry setup for FastAPI               |
# | PLIK: monitoring/otel_setup.py                             |
# | ROLA: Opcjonalna inicjalizacja OpenTelemetry dla FastAPI     |
# +-------------------------------------------------------------+

"""
PL: Pomocnik OTel. Jeśli `OTEL_ENABLED=1`, próbuje skonfigurować OTLP exporter
    (adres z `OTEL_EXPORTER_OTLP_ENDPOINT`) i zainstrumentować FastAPI.

EN: OTel helper. If `OTEL_ENABLED=1`, tries to configure OTLP exporter
    (endpoint from `OTEL_EXPORTER_OTLP_ENDPOINT`) and instrument FastAPI.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import os
from typing import Any


def setup_fastapi_otel(app: Any) -> None:
    if (os.getenv("OTEL_ENABLED") or "").strip() not in {"1", "true", "True"}:
        return
    try:
        from opentelemetry import trace  # type: ignore
        from opentelemetry.exporter.otlp.proto.http.trace_exporter import (  # type: ignore
            OTLPSpanExporter,
        )
        from opentelemetry.instrumentation.fastapi import FastAPIInstrumentor  # type: ignore
        from opentelemetry.sdk.resources import SERVICE_NAME, Resource  # type: ignore
        from opentelemetry.sdk.trace import TracerProvider  # type: ignore
        from opentelemetry.sdk.trace.export import (  # type: ignore
            BatchSpanProcessor,
        )

        svc = os.getenv("OTEL_SERVICE_NAME") or "certeus-api"
        res = Resource(attributes={SERVICE_NAME: svc})
        provider = TracerProvider(resource=res)
        ep = os.getenv("OTEL_EXPORTER_OTLP_ENDPOINT") or "http://localhost:4318"
        exporter = OTLPSpanExporter(endpoint=f"{ep}/v1/traces")
        provider.add_span_processor(BatchSpanProcessor(exporter))
        trace.set_tracer_provider(provider)
        FastAPIInstrumentor.instrument_app(app, tracer_provider=provider)
    except Exception:
        # best-effort; lack of OTel deps should not break app
        return


def set_span_attrs(attrs: dict[str, Any]) -> None:
    try:
        from opentelemetry import trace  # type: ignore

        span = trace.get_current_span()
        for k, v in attrs.items():
            try:
                span.set_attribute(str(k), v)
            except Exception:
                continue
    except Exception:
        pass


# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
