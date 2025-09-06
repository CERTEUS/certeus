#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/e2e/test_pfs_mount_inspect.py                  |
# | ROLE: E2E test module.                                      |
# | PLIK: tests/e2e/test_pfs_mount_inspect.py                  |
# | ROLA: Moduł testów E2E.                                     |
# +-------------------------------------------------------------+

"""
PL: E2E: (mock) mount → materialize → inspect xattrs → unmount.
EN: E2E: (mock) mount → materialize → inspect xattrs → unmount.
"""

from __future__ import annotations

import os
from pathlib import Path
import tempfile

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_pfs_mount_materialize_inspect_unmount_e2e() -> None:
    client = TestClient(app)
    with tempfile.TemporaryDirectory() as tmp:
        os.environ["PROOFS_FS_ROOT"] = tmp
        # mount (mock)
        r1 = client.post("/v1/pfs/mount", json={})
        assert r1.status_code == 200 and (r1.json().get("mounted") is True)
        mid = r1.json().get("mount_id")
        assert isinstance(mid, str) and mid

        # materialize a stub artifact
        uri = "pfs://mail/E2E/flow.txt"
        r2 = client.post(
            "/v1/pfs/materialize", json={"uri": uri, "meta": {"note": "e2e"}}
        )
        assert r2.status_code == 200
        path = Path(r2.json().get("path") or "")
        assert path.exists() and path.is_file()

        # inspect xattrs
        r3 = client.get("/v1/pfs/xattrs", params={"uri": uri})
        assert r3.status_code == 200
        xattrs = r3.json().get("xattrs") or {}
        assert isinstance(xattrs.get("pnip"), str) and xattrs["pnip"].startswith(
            "sha256:"
        )

        # unmount (mock)
        r4 = client.post("/v1/pfs/unmount", json={"mount_id": mid})
        assert r4.status_code == 200 and (r4.json().get("unmounted") is True)
