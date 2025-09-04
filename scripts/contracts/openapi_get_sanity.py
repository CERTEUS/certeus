#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/contracts/openapi_get_sanity.py             |
# | ROLE: Contract: GET endpoints sanity                         |
# | PLIK: scripts/contracts/openapi_get_sanity.py             |
# | ROLA: Kontrakt: sanity GET endpointów                        |
# +-------------------------------------------------------------+

"""
PL: Sanity kontraktu na bazie OpenAPI runtime: iteruje po ścieżkach GET bez
    parametrów ścieżki i wzywa je in‑proc. Raportuje 2xx/nie‑2xx.

EN: Runtime OpenAPI GET sanity: iterates GET paths without path params and
    calls them in‑proc. Reports 2xx/non‑2xx.
"""

from __future__ import annotations

import os
from typing import Any

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def _load_runtime_spec() -> dict[str, Any]:
    c = TestClient(app)
    r = c.get("/openapi.json")
    return r.json() if r.status_code == 200 else {}


def _get_get_paths(spec: dict[str, Any]) -> list[str]:
    out: list[str] = []
    paths = spec.get("paths") or {}
    if not isinstance(paths, dict):
        return out
    for p, ops in paths.items():
        if not isinstance(ops, dict):
            continue
        if "get" in {k.lower() for k in ops.keys()} and "{" not in p and "}" not in p:
            out.append(str(p))
    return out


def main() -> int:  # pragma: no cover
    spec = _load_runtime_spec()
    gets = _get_get_paths(spec)
    c = TestClient(app)
    bad: list[str] = []
    for p in gets:
        r = c.get(p)
        if not (200 <= r.status_code < 300):
            bad.append(f"{p} -> {r.status_code}")
    enforce = (os.getenv("ENFORCE_OPENAPI_GET_SANITY") or "").strip() in {"1", "true", "True"}
    if bad:
        print("OpenAPI GET sanity: FAIL")
        for b in bad:
            print(" -", b)
        return 1 if enforce else 0
    print(f"OpenAPI GET sanity: OK ({len(gets)} endpoints)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
