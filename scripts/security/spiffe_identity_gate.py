#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/security/spiffe_identity_gate.py             |
# | ROLE: Report SPIFFE/SPIRE identity presence (report-only)    |
# | PLIK: scripts/security/spiffe_identity_gate.py             |
# | ROLA: Raport obecności tożsamości SPIFFE/SPIRE (report-only) |
# +-------------------------------------------------------------+

"""
PL: Sprawdza minimalną obecność tożsamości SPIFFE/SPIRE:
    - plik `infra/spiffe/svid.json` (SVID), lub
    - zmienne środowiskowe `SPIFFE_ID`, `TRUST_DOMAIN`.
Zapisuje raport do `out/spiffe_report.json` (status: present/missing) — report-only.

EN: Checks minimal presence of SPIFFE/SPIRE identity:
    - file `infra/spiffe/svid.json` (SVID), or
    - env vars `SPIFFE_ID`, `TRUST_DOMAIN`.
Writes report to `out/spiffe_report.json` (status: present/missing) — report-only.
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
    svid_path = repo / "infra" / "spiffe" / "svid.json"
    present = False
    info: dict[str, Any] = {"source": None}
    if svid_path.exists():
        try:
            svid = json.loads(svid_path.read_text(encoding="utf-8"))
            td = svid.get("trust_domain") or svid.get("td")
            sid = svid.get("spiffe_id") or svid.get("id")
            info = {"source": "file", "trust_domain": td, "spiffe_id": sid}
            present = True
        except Exception as e:
            info = {"source": "file", "error": str(e)}
    else:
        sid = os.getenv("SPIFFE_ID")
        td = os.getenv("TRUST_DOMAIN")
        if sid and td:
            present = True
            info = {"source": "env", "trust_domain": td, "spiffe_id": sid}
        else:
            info = {"source": "none"}
    report = {"present": present, **info}
    (out / "spiffe_report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
