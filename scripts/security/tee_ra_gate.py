#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/security/tee_ra_gate.py                      |
# | ROLE: Report TEE RA attestation presence (report-only)       |
# | PLIK: scripts/security/tee_ra_gate.py                      |
# | ROLA: Raport obecności atestacji TEE RA (report-only)        |
# +-------------------------------------------------------------+

"""
PL: Sprawdza obecność atestacji TEE (RA) w `infra/tee/attestation.json` lub
    odcisku palca w `TEE_RA_FINGERPRINT`. Raport do `out/tee_ra.json`.

EN: Reports presence of TEE RA attestation under `infra/tee/attestation.json`
    or fingerprint via `TEE_RA_FINGERPRINT`. Writes `out/tee_ra.json`.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)
    att = repo / "infra" / "tee" / "attestation.json"
    present = False
    info: dict[str, Any] = {"source": None}
    if att.exists():
        try:
            js = json.loads(att.read_text(encoding="utf-8"))
            meas = js.get("measurement") or js.get("mrenclave") or js.get("fingerprint")
            present = bool(meas)
            info = {"source": "file", "measurement": meas}
        except Exception as e:
            info = {"source": "file", "error": str(e)}
    else:
        fp = os.getenv("TEE_RA_FINGERPRINT")
        if fp:
            present = True
            info = {"source": "env", "measurement": fp}
        else:
            info = {"source": "none"}
    (out / "tee_ra.json").write_text(json.dumps({"present": present, **info}, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
