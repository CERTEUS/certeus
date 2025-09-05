#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_xattrs.py                    |
# | ROLE: Project test module.                                  |
# | PLIK: tests/services/test_pfs_xattrs.py                    |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Testy xattrs (PNIP/PCO) — endpoint i warstwa core.
EN: Xattrs (PNIP/PCO) tests — endpoint and core layer.
"""

from __future__ import annotations

from pathlib import Path
import re
import tempfile

from fastapi.testclient import TestClient

from core.pfs.xattrs import get_xattrs_for_path
from services.api_gateway.main import app

_RE_SHA256 = re.compile(r"^sha256:[0-9a-f]{64}$")


def test_pfs_xattrs_endpoint_and_core() -> None:
    client = TestClient(app)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        # point ProofFS root
        import os

        os.environ["PROOFS_FS_ROOT"] = str(root)

        # prepare file
        p = root / "mail" / "MID-X" / "doc.txt"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("HELLO-XATTRS", encoding="utf-8")

        # Core xattrs
        xa = get_xattrs_for_path(p)
        assert isinstance(xa, dict)
        assert _RE_SHA256.match(xa.get("pnip", ""))
        pnip_hex = xa["pnip"].split(":", 1)[1]
        assert (xa.get("pco") or {}).get("smt2_hash") == pnip_hex

        # Endpoint xattrs
        uri = "pfs://mail/MID-X/doc.txt"
        r = client.get("/v1/pfs/xattrs", params={"uri": uri})
        assert r.status_code == 200
        body = r.json()
        assert body.get("uri") == uri
        x = body.get("xattrs") or {}
        assert _RE_SHA256.match(x.get("pnip", ""))
        assert (x.get("pco") or {}).get("smt2_hash") == x.get("pnip").split(":", 1)[1]
