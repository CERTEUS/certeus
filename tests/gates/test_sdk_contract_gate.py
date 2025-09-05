#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_sdk_contract_gate.py                |
# | ROLE: Enterprise gate test: SDK/OpenAPI contract           |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path

from scripts.gates.sdk_contract_gate import main as sdk_gate_main


def test_sdk_contract_gate_report_ok(tmp_path: Path, monkeypatch) -> None:
    # Run in repo root; the gate writes to ./out
    monkeypatch.chdir(Path(".").resolve())
    rc = sdk_gate_main()
    assert rc == 0
    rep = json.loads(Path("out/sdk_contract_report.json").read_text(encoding="utf-8"))
    # No errors expected in current tree
    assert rep.get("errors") == []
    # Fetch live spec and validate presence of key operationIds
    from fastapi.testclient import TestClient  # local import to avoid global dependency at module load

    from services.api_gateway.main import app  # type: ignore

    c = TestClient(app)
    spec = c.get("/openapi.json").json()
    paths = spec.get("paths") or {}
    op_ids = set()
    for _, methods in paths.items():
        for _, op in (methods or {}).items():
            oi = (op or {}).get("operationId")
            if oi:
                op_ids.add(str(oi))
    assert "pfs_list_entries" in op_ids
    assert "pfs_get_xattrs" in op_ids
    assert "pfs_materialize" in op_ids
