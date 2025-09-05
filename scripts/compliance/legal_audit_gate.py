#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/compliance/legal_audit_gate.py               |
# | ROLE: Legal audit checklist validator (report-only)          |
# | PLIK: scripts/compliance/legal_audit_gate.py               |
# | ROLA: Walidator checklist audytu prawnego (report-only)      |
# +-------------------------------------------------------------+

"""
PL: Sprawdza checklistę audytu prawnego w `docs/compliance/legal_audit_checklist.md`.
    Wymagane sekcje: Scope, Controls, Evidence, Findings, Remediations.
    Raport: `out/legal_audit.json`.

EN: Validates legal audit checklist under `docs/compliance/legal_audit_checklist.md`.
    Required sections: Scope, Controls, Evidence, Findings, Remediations.
    Report: `out/legal_audit.json`.
"""

from __future__ import annotations

import json
from pathlib import Path

SECTIONS = ["## Scope", "## Controls", "## Evidence", "## Findings", "## Remediations"]


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)
    p = repo / "docs" / "compliance" / "legal_audit_checklist.md"
    text = p.read_text(encoding="utf-8") if p.exists() else ""
    missing = [s for s in SECTIONS if s not in text]
    rep = {"path": str(p), "missing": missing, "ok": not missing}
    (out / "legal_audit.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
