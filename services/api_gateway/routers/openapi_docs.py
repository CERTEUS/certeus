#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/openapi_docs.py         |
# | ROLE: Serve docs OpenAPI as JSON                            |
# | PLIK: services/api_gateway/routers/openapi_docs.py         |
# | ROLA: Zwraca OpenAPI z docs/api/openapi.yaml jako JSON      |
# +-------------------------------------------------------------+
"""
PL: Router FastAPI – zwraca specyfikację OpenAPI z repozytorium (docs/api/openapi.yaml)
    w formacie JSON do porównania z runtime.

EN: FastAPI router – serves the repository OpenAPI (docs/api/openapi.yaml) as
    JSON for comparison with the runtime schema.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path
from typing import Any

from fastapi import APIRouter
import yaml

# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/openapi", tags=["openapi"])


@router.get("/docs", summary="Get repository OpenAPI (docs) as JSON")
def get_docs_openapi() -> dict[str, Any]:
    root = Path(__file__).resolve().parents[3]
    p = root / "docs" / "api" / "openapi.yaml"
    try:
        data = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
        if not isinstance(data, dict):  # pragma: no cover – defensive
            return {}
        return data
    except Exception:
        return {}


# === TESTY / TESTS ===
