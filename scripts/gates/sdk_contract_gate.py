#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/sdk_contract_gate.py                   |
# | ROLE: Report-only gate: SDK/OpenAPI contract sanity        |
# | PLIK: scripts/gates/sdk_contract_gate.py                   |
# | ROLA: Bramka (report-only): sanity kontraktu SDK/OpenAPI   |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path
import sys
from typing import Any

from fastapi.testclient import TestClient


def _ok(msg: str) -> None:
    print(msg)


def _fail(msg: str) -> None:
    print(msg, file=sys.stderr)


def _ensure(cond: bool, msg: str, errors: list[str]) -> None:
    if not cond:
        errors.append(msg)


def _has_ts_sdk(repo: Path) -> bool:
    t = repo / "sdk" / "ts" / "src" / "client.ts"
    try:
        if t.exists():
            s = t.read_text(encoding="utf-8")
            # minimal markers
            return ("function pfsList" in s) and ("function pfsXattrs" in s)
    except Exception:
        return False
    return False


def _has_go_sdk(repo: Path) -> bool:
    g = repo / "sdk" / "go" / "certeus" / "certeus.go"
    try:
        if g.exists():
            s = g.read_text(encoding="utf-8")
            return ("func (c *Client) PFSList" in s) and ("func (c *Client) PFSXattrs" in s)
    except Exception:
        return False
    return False


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)

    # Import app lazily to avoid circular imports in CI
    from services.api_gateway.main import app  # type: ignore

    client = TestClient(app)
    r = client.get("/openapi.json")
    if r.status_code != 200:
        _fail("openapi: failed to fetch /openapi.json")
        return 0  # report-only

    spec: dict[str, Any] = r.json()
    paths = set((spec.get("paths") or {}).keys())
    ops = {}
    for p, m in (spec.get("paths") or {}).items():
        for method, op in (m or {}).items():
            if isinstance(op, dict) and op.get("operationId"):
                ops[op["operationId"]] = (method.lower(), p)

    errors: list[str] = []
    # Required minimal operations for SDK 2.0 stub
    required_ops = {
        "pfs_list_entries",
        "pfs_get_xattrs",
        "pfs_materialize",
        "publish_proofgate_publish",  # fallback if generator names it this way
    }
    # allow either proofgate publish opId or any POST path under /v1/proofgate/publish
    has_publish = any(p.endswith("/v1/proofgate/publish") and m == "post" for (_id, (m, p)) in ops.items()) or (
        "publish_proofgate_publish" in ops or "proofgate_publish" in ops
    )

    for op_id in ("pfs_list_entries", "pfs_get_xattrs", "pfs_materialize"):
        _ensure(op_id in ops, f"missing operationId: {op_id}", errors)
    _ensure(has_publish, "missing publish endpoint (/v1/proofgate/publish)", errors)

    # SDK stubs presence
    _ensure(_has_ts_sdk(repo), "missing or incomplete TS SDK stub (sdk/ts/src/client.ts)", errors)
    _ensure(_has_go_sdk(repo), "missing or incomplete Go SDK stub (sdk/go/c\u0301erteus/certeus.go)", errors)

    report = {
        "openapi_paths": len(paths),
        "ops_present": sorted(list(ops.keys()))[:20],
        "errors": errors,
    }
    (out / "sdk_contract_report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    if errors:
        _fail("SDK Contract Gate: WARN " + json.dumps(errors))
    else:
        (out / "sdk_contract_ok.txt").write_text("ok\n", encoding="utf-8")
        _ok("SDK Contract Gate: OK")
    return 0  # report-only


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

