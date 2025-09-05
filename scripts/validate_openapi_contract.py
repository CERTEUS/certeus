#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/validate_openapi_contract.py                  |
# | ROLE: Validate runtime OpenAPI vs docs contract             |
# | PLIK: scripts/validate_openapi_contract.py                  |
# | ROLA: Waliduj runtime OpenAPI względem kontraktu w docs     |
# +-------------------------------------------------------------+
"""
PL: Porównuje runtime `/openapi.json` (in‑proc) ze specyfikacją w `docs/api/openapi.yaml`.
    Sprawdza minimalną zgodność kontraktową: istnienie ścieżek i podstawowych metadanych.

EN: Compares runtime `/openapi.json` (in‑proc) with `docs/api/openapi.yaml`.
    Enforces minimal contract: presence of documented paths and basic metadata.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path
import sys
from typing import Any

import yaml

# Import app inline (no server needed)
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from services.api_gateway.main import app  # noqa: E402

# === LOGIKA / LOGIC ===


def _read_docs_spec(path: Path) -> dict[str, Any]:
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise RuntimeError("Invalid OpenAPI YAML (not a mapping)")
    return data


def _collect_methods(path_item: dict[str, Any]) -> set[str]:
    return {k.lower() for k in path_item.keys() if k.lower() in {"get", "post", "put", "patch", "delete"}}


def main() -> int:
    docs_path = REPO_ROOT / "docs" / "api" / "openapi.yaml"
    docs = _read_docs_spec(docs_path)
    runtime = app.openapi()

    errs: list[str] = []

    # Basic keys
    for key in ("openapi", "info", "paths"):
        if key not in runtime:
            errs.append(f"runtime missing '{key}'")

    # Version/compat signals (W15 D71)
    info = runtime.get("info", {})
    if "x-compat" not in info:
        errs.append("runtime info.x-compat missing")

    # Each documented path must exist at runtime; methods check is best-effort
    doc_paths: dict[str, Any] = docs.get("paths", {}) or {}
    rt_paths: dict[str, Any] = runtime.get("paths", {}) or {}

    for p, item in doc_paths.items():
        if p not in rt_paths:
            errs.append(f"missing path in runtime: {p}")
            continue
        doc_methods = _collect_methods(item or {})
        rt_methods = _collect_methods(rt_paths.get(p) or {})
        missing = sorted(doc_methods - rt_methods)
        if missing:
            errs.append(f"missing methods for {p}: {', '.join(missing)}")

    if errs:
        print("\nContract check FAILED:\n - " + "\n - ".join(errs))
        return 1

    print("Contract check OK: runtime OpenAPI matches documented paths.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
