#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/contracts/check_runtime_operation_id_dups.py |
# | ROLE: Contract tool: detect duplicate operationId in runtime |
# | PLIK: scripts/contracts/check_runtime_operation_id_dups.py |
# | ROLA: Narzędzie kontraktu: wykryj duplikaty operationId      |
# +-------------------------------------------------------------+
"""
PL: Narzędzie kontraktowe: pobiera `/openapi.json` z aplikacji in‑proc i
    raportuje duplikaty `operationId`. Zwraca kod 1 przy wykryciu dublowań.

EN: Contract tool: fetches `/openapi.json` from the app in‑proc and reports
    duplicate `operationId`s. Exits with code 1 on duplicates.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from typing import Any

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === LOGIKA / LOGIC ===


def _load_openapi() -> dict[str, Any]:
    c = TestClient(app)
    r = c.get("/openapi.json")
    return r.json() if r.status_code == 200 else {}


def find_dups(spec: dict[str, Any]) -> dict[str, list[tuple[str, str]]]:
    d: dict[str, list[tuple[str, str]]] = {}
    paths = spec.get("paths") or {}
    if not isinstance(paths, dict):
        return {}
    for path, ops in paths.items():
        if not isinstance(ops, dict):
            continue
        for method, op in ops.items():
            if not isinstance(op, dict):  # skip non-objects
                continue
            opid = op.get("operationId")
            if not opid:
                continue
            d.setdefault(str(opid), []).append((str(method).upper(), str(path)))
    return {k: v for k, v in d.items() if len(v) > 1}


def main() -> int:  # pragma: no cover (tool)
    spec = _load_openapi()
    dups = find_dups(spec)
    if not dups:
        print("Runtime operationId check: OK (no duplicates)")
        return 0
    print("Runtime operationId check: DUPLICATES FOUND")
    for k, v in sorted(dups.items()):
        print(" -", k, "->", ", ".join([f"{m} {p}" for m, p in v]))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
