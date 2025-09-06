#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/security/kms_rotation_gate.py                |
# | ROLE: Report KMS/key rotation policy presence (report-only)  |
# | PLIK: scripts/security/kms_rotation_gate.py                |
# | ROLA: Raport obecności polityki rotacji kluczy (report-only) |
# +-------------------------------------------------------------+

"""
PL: Sprawdza, czy istnieją podstawowe artefakty polityki rotacji kluczy:
    - `security/keys/metadata.json` (z polami `current`, `previous`, `algo`), lub
    - pliki `security/keys/current.*` oraz `security/keys/prev.*`.
Zapisuje raport do `out/kms_rotation.json`. Report-only (nie failuje ci-gates).

EN: Checks presence of key rotation policy artifacts:
    - `security/keys/metadata.json` (with `current`, `previous`, `algo`) or
    - files `security/keys/current.*` and `security/keys/prev.*`.
Writes report to `out/kms_rotation.json`. Report-only.
"""

from __future__ import annotations

import glob
import json
from pathlib import Path
from typing import Any


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)
    base = repo / "security" / "keys"
    rep: dict[str, Any] = {"present": False, "mode": None}
    meta = base / "metadata.json"
    if meta.exists():
        try:
            js = json.loads(meta.read_text(encoding="utf-8"))
            cur = js.get("current")
            prev = js.get("previous")
            algo = js.get("algo")
            if cur and algo:
                rep |= {
                    "present": True,
                    "mode": "metadata",
                    "current": cur,
                    "previous": prev,
                    "algo": algo,
                }
        except Exception as e:
            rep = {"present": False, "mode": "metadata", "error": str(e)}
    else:
        cur = sorted(glob.glob(str(base / "current.*")))
        prev = sorted(glob.glob(str(base / "prev.*")))
        if cur:
            rep |= {
                "present": True,
                "mode": "files",
                "current_files": cur,
                "prev_files": prev,
            }
    (out / "kms_rotation.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
