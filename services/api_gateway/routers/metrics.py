#!/usr/bin/env python3
from __future__ import annotations

from fastapi import APIRouter, Response
from prometheus_client import CONTENT_TYPE_LATEST, generate_latest

router = APIRouter(prefix="", tags=["metrics"])


@router.get("/metrics")
def metrics() -> Response:
    # Use the default global registry
    data = generate_latest()  # type: ignore[arg-type]
    return Response(content=data, media_type=CONTENT_TYPE_LATEST)
