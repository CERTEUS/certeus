#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/api/test_openapi_contract_runtime.py           |
# | ROLE: Runtime OpenAPI vs docs contract test                |
# | PLIK: tests/api/test_openapi_contract_runtime.py           |
# | ROLA: Test kontraktu OpenAPI runtime vs dokumentacja       |
# +-------------------------------------------------------------+
"""
PL: Sprawdza, czy OpenAPI runtime zawiera ścieżki z `docs/api/openapi.yaml`
    oraz metadane kompatybilności (x-compat).

EN: Verifies that runtime OpenAPI contains paths from `docs/api/openapi.yaml`
    and compatibility metadata (x-compat).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path
from typing import Any

import yaml
import warnings

# Suppress noisy FastAPI OpenAPI duplicate operation id warnings during schema build
warnings.filterwarnings("ignore", message="Duplicate Operation ID*", category=UserWarning)

from services.api_gateway.main import app


def _collect_methods(item: dict[str, Any]) -> set[str]:
    return {k.lower() for k in item.keys() if k.lower() in {"get", "post", "put", "patch", "delete"}}


def _norm_path(p: str) -> str:
    # Normalize path parameter names: /x/{rid} == /x/{case_id}
    import re

    return re.sub(r"\{[^/]+\}", "{}", p)


def test_runtime_openapi_matches_docs_contract() -> None:
    docs = yaml.safe_load(Path("docs/api/openapi.yaml").read_text(encoding="utf-8"))
    runtime = app.openapi()

    assert isinstance(runtime, dict)
    assert "openapi" in runtime and "info" in runtime and "paths" in runtime
    assert isinstance(runtime["info"], dict)
    assert "x-compat" in runtime["info"]

    doc_paths: dict[str, Any] = docs.get("paths", {}) or {}
    rt_paths: dict[str, Any] = runtime.get("paths", {}) or {}

    # Paths to ignore for runtime parity (wired in different service)
    SKIP: set[str] = {"/defx/reason"}

    doc_norm = {_norm_path(p): p for p in doc_paths.keys() if p not in SKIP}
    rt_norm = {_norm_path(p): p for p in rt_paths.keys()}
    missing_paths: list[str] = [orig for norm, orig in doc_norm.items() if norm not in rt_norm]
    assert not missing_paths, f"Missing runtime paths: {missing_paths}"

    # Best-effort method presence check
    for p, item in doc_paths.items():
        if p in SKIP:
            continue
        # method comparison with normalization
        rt_methods = _collect_methods(rt_paths.get(rt_norm.get(_norm_path(p), "")) or {})
        doc_methods = _collect_methods(item or {})
        assert doc_methods.issubset(rt_methods), f"Missing methods for {p}: {sorted(doc_methods - rt_methods)}"
