#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/asset_integrity_gate.py                |
# | ROLE: CI gate — PNIP/PCO integrity on samples (enforced)   |
# | PLIK: scripts/gates/asset_integrity_gate.py                |
# | ROLA: Bramka CI — spójność PNIP/PCO na próbkach (egzekwowana) |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
import tempfile
from typing import Any

from core.pfs.materialize import materialize_mail_attachment
from core.pfs.xattrs import get_xattrs_for_path


def _ok(msg: str) -> None:
    print(msg)


def _fail(msg: str) -> None:
    print(msg, file=sys.stderr)
    sys.exit(1)


def _check_consistency(xattrs: dict[str, Any]) -> tuple[bool, str]:
    pnip = xattrs.get("pnip")
    pco = xattrs.get("pco") or {}

    if not isinstance(pnip, str) or not pnip.startswith("sha256:") or len(pnip.split(":",1)[1]) != 64:
        return False, "PNIP must be sha256:<64-hex>"
    pnip_hex = pnip.split(":", 1)[1]

    # PCO minimal structure and smt2_hash match
    smt2 = (pco or {}).get("smt2_hash")
    rid = (pco or {}).get("rid")
    if not isinstance(smt2, str) or smt2.lower() != pnip_hex.lower():
        return False, "PCO.smt2_hash must equal PNIP hex"
    if not isinstance(rid, str) or not rid:
        return False, "PCO.rid missing"
    return True, "ok"


def main() -> None:
    out_dir = Path("out")
    out_dir.mkdir(parents=True, exist_ok=True)

    # Use an isolated temp root to avoid repo pollution
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        os.environ["PROOFS_FS_ROOT"] = str(root)

        # Create sample assets
        a = materialize_mail_attachment("GATE-1", "a.txt", meta={"note": "gate-sample"})
        b = materialize_mail_attachment("GATE-2", "b.txt", meta={"note": "gate-sample"})

        # Compute xattrs and validate
        xa = get_xattrs_for_path(a)
        xb = get_xattrs_for_path(b)

        ok_a, msg_a = _check_consistency(xa)
        ok_b, msg_b = _check_consistency(xb)

        report = {"a": {"ok": ok_a, "msg": msg_a}, "b": {"ok": ok_b, "msg": msg_b}}
        (out_dir / "asset_integrity.json").write_text(json.dumps(report, indent=2), encoding="utf-8")

        if not (ok_a and ok_b):
            _fail(f"Asset-Integrity Gate failed: {report}")

    _ok("Asset-Integrity Gate: OK")
    (out_dir / "asset_integrity_ok.txt").write_text("ok\n", encoding="utf-8")


if __name__ == "__main__":  # pragma: no cover
    main()
