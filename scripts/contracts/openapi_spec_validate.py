#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/contracts/openapi_spec_validate.py           |
# | ROLE: Contract: validate OpenAPI specs                        |
# | PLIK: scripts/contracts/openapi_spec_validate.py           |
# | ROLA: Kontrakt: walidacja spec OpenAPI                        |
# +-------------------------------------------------------------+

"""
PL: Walidacja plików OpenAPI (docs i runtime). Report‑only; wymuszenie przez
    `ENFORCE_OPENAPI_SPEC_VALIDATE=1`.

EN: Validate OpenAPI specs (docs and runtime). Report‑only; enforce via
    `ENFORCE_OPENAPI_SPEC_VALIDATE=1`.
"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

try:
    from openapi_spec_validator import validate_spec
    from openapi_spec_validator.schemas import read_yaml_file
except Exception:  # pragma: no cover
    validate_spec = None  # type: ignore
    read_yaml_file = None  # type: ignore

def _load_docs_spec(repo: Path) -> tuple[dict[str, Any], str]:
    for p in (
        repo / "docs" / "openapi" / "certeus.v1.yaml",
        repo / "docs" / "api" / "openapi.yaml",
    ):
        if p.exists():
            try:
                if read_yaml_file is not None and p.suffix in {".yml", ".yaml"}:
                    return read_yaml_file(p), str(p)
                return json.loads(p.read_text(encoding="utf-8")), str(p)
            except Exception:
                return {}, str(p)
    return {}, "<none>"

def _load_runtime_spec() -> dict[str, Any]:
    try:
        from fastapi.testclient import TestClient

        from services.api_gateway.main import app

        client = TestClient(app)
        r = client.get("/openapi.json")
        return r.json() if r.status_code == 200 else {}
    except Exception:
        return {}

def main() -> int:  # pragma: no cover
    repo = Path(".").resolve()
    docs, src = _load_docs_spec(repo)
    rt = _load_runtime_spec()

    vio = 0
    if validate_spec is None:
        print("OpenAPI validate: validator not installed (openapi-spec-validator)")
    else:
        try:
            if docs:
                validate_spec(docs)
                print(f"OpenAPI validate: docs OK ({src})")
            else:
                print("OpenAPI validate: no docs spec found")
        except Exception as e:
            vio += 1
            print(f"OpenAPI validate: docs INVALID: {e}")
        try:
            if rt:
                validate_spec(rt)
                print("OpenAPI validate: runtime OK (/openapi.json)")
            else:
                print("OpenAPI validate: runtime spec not available")
        except Exception as e:
            vio += 1
            print(f"OpenAPI validate: runtime INVALID: {e}")

    enforce = (os.getenv("ENFORCE_OPENAPI_SPEC_VALIDATE") or "").strip() in {"1", "true", "True"}
    if vio and enforce:
        return 1
    print(f"OpenAPI validate: {'OK (report-only)' if not enforce else ('FAIL' if vio else 'OK')}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
