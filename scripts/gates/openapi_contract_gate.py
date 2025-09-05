#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/openapi_contract_gate.py               |
# | ROLE: Project gate script.                                   |
# | PLIK: scripts/gates/openapi_contract_gate.py               |
# | ROLA: Skrypt bramki projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Bramką kontraktu OpenAPI (report‑only). Porównuje runtime `/openapi.json`
    z plikiem specyfikacji (`docs/openapi/certeus.v1.yaml` lub `docs/api/openapi.yaml`).
    Raportuje brakujące ścieżki/metody w dokumencie vs runtime (subset check).

EN: OpenAPI contract gate (report‑only). Compares runtime `/openapi.json` with
    repo spec (`docs/openapi/certeus.v1.yaml` or `docs/api/openapi.yaml`).
    Reports missing paths/methods in docs vs runtime (subset check).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Iterable
import json
import os
from pathlib import Path

try:
    import yaml  # type: ignore
except Exception:  # pragma: no cover
    yaml = None  # type: ignore

def _load_docs_spec(repo: Path) -> dict:
    for p in (
        repo / "docs" / "openapi" / "certeus.v1.yaml",
        repo / "docs" / "api" / "openapi.yaml",
    ):
        if p.exists():
            try:
                if yaml is not None and p.suffix in {".yml", ".yaml"}:
                    return yaml.safe_load(p.read_text(encoding="utf-8")) or {}
                return json.loads(p.read_text(encoding="utf-8"))
            except Exception:
                return {}
    return {}

def _normalize_paths(spec: dict) -> dict[str, Iterable[str]]:
    paths = spec.get("paths") or {}
    out: dict[str, Iterable[str]] = {}
    if not isinstance(paths, dict):
        return out
    for p, ops in paths.items():
        if not isinstance(ops, dict):
            continue
        methods = [m.lower() for m in ops.keys() if isinstance(m, str)]
        out[str(p)] = sorted(set(methods))
    return out

def check(repo_root: str | Path | None = None) -> tuple[list[str], list[str]]:
    """PL/EN: (violations, warnings) — violations: endpoints present in runtime but missing in docs."""
    repo = Path(repo_root or ".").resolve()

    # Runtime spec via in-proc app
    try:
        from fastapi.testclient import TestClient

        from services.api_gateway.main import app

        client = TestClient(app)
        r = client.get("/openapi.json")
        runtime = r.json() if r.status_code == 200 else {}
    except Exception:
        runtime = {}

    docs = _load_docs_spec(repo)

    rt_paths = _normalize_paths(runtime)
    dc_paths = _normalize_paths(docs)

    violations: list[str] = []
    warnings: list[str] = []

    # Docs should cover runtime (subset check)
    for path, methods in rt_paths.items():
        dmethods = dc_paths.get(path, [])
        missing = [m for m in methods if m not in dmethods]
        if missing:
            violations.append(f"Missing in docs: {path} methods {missing}")

    # Warn if docs have paths not present in runtime (drift)
    for path in dc_paths.keys():
        if path not in rt_paths:
            warnings.append(f"Docs define path not in runtime: {path}")

    return violations, warnings

def main() -> int:  # pragma: no cover (integration)
    vio, warn = check()
    if warn:
        print("OpenAPI Contract: WARNINGS")
        for w in warn:
            print(" -", w)
    if vio:
        print("OpenAPI Contract: VIOLATIONS")
        for v in vio:
            print(" -", v)
    enforce = (os.getenv("ENFORCE_OPENAPI_CONTRACT") or "").strip() in {"1", "true", "True"}
    if vio and enforce:
        return 1
    print(
        f"OpenAPI Contract: {'OK (report-only)' if not enforce else ('FAIL' if vio else 'OK')} — "
        f"{len(vio)} violations, {len(warn)} warnings"
    )
    return 0

# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
