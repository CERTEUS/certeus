#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/compliance_mapping_gate.py             |
# | ROLE: Project gate script.                                   |
# | PLIK: scripts/gates/compliance_mapping_gate.py             |
# | ROLA: Skrypt bramki projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Bramka mapowania zgodności (DPIA/ISO 27001/SOC2) — report‑only domyślnie.
    Weryfikuje istnienie i minimalną zawartość dokumentów:
      - docs/compliance/dpia.md (Purpose/Lawful basis/Data minimization/Security/Risk mitigation)
      - docs/compliance/iso27001_checklist.md (A.5/A.8/A.12/A.14/A.18)
      - docs/compliance/soc2_checklist.md (Security/Availability/Confidentiality)

EN: Compliance mapping gate (report‑only). Verifies presence and minimal content
    for DPIA/ISO27001/SOC2 documents listed above.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from pathlib import Path

def _contains_all(text: str, needles: list[str]) -> bool:
    t = text.lower()
    return all(n.lower() in t for n in needles)

def check(root: str | Path | None = None) -> tuple[list[str], list[str]]:
    """PL/EN: Zwraca (violations, warnings)."""
    repo = Path(root or ".").resolve()
    vio: list[str] = []
    warn: list[str] = []

    # DPIA
    dpia = repo / "docs" / "compliance" / "dpia.md"
    if not dpia.exists():
        vio.append("missing docs/compliance/dpia.md")
    else:
        txt = dpia.read_text(encoding="utf-8", errors="ignore")
        if not _contains_all(txt, ["purpose", "lawful basis", "minimization", "security", "risk"]):
            warn.append("dpia.md: missing some expected sections")

    # ISO 27001
    iso = repo / "docs" / "compliance" / "iso27001_checklist.md"
    if not iso.exists():
        vio.append("missing docs/compliance/iso27001_checklist.md")
    else:
        txt = iso.read_text(encoding="utf-8", errors="ignore")
        if not _contains_all(txt, ["A.5", "A.8", "A.12", "A.14", "A.18"]):
            warn.append("iso27001_checklist.md: expected A.5/A.8/A.12/A.14/A.18 entries")

    # SOC2
    soc2 = repo / "docs" / "compliance" / "soc2_checklist.md"
    if not soc2.exists():
        vio.append("missing docs/compliance/soc2_checklist.md")
    else:
        txt = soc2.read_text(encoding="utf-8", errors="ignore")
        if not _contains_all(txt, ["security", "availability", "confidentiality"]):
            warn.append("soc2_checklist.md: expected Security/Availability/Confidentiality entries")

    return vio, warn

def main() -> int:  # pragma: no cover (integration)
    vio, warn = check()
    if warn:
        print("Compliance: WARNINGS")
        for w in warn:
            print(" -", w)
    if vio:
        print("Compliance: VIOLATIONS")
        for v in vio:
            print(" -", v)
    enforce = (os.getenv("ENFORCE_COMPLIANCE_MAPPING") or "").strip() in {"1", "true", "True"}
    if vio and enforce:
        return 1
    print(
        f"Compliance Mapping: {'OK (report-only)' if not enforce else ('FAIL' if vio else 'OK')} — "
        f"{len(vio)} violations, {len(warn)} warnings"
    )
    return 0

# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
