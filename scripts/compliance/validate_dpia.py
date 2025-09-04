#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/compliance/validate_dpia.py                  |
# | ROLE: Validate DPIA/DPA docs for required sections           |
# | PLIK: scripts/compliance/validate_dpia.py                  |
# | ROLA: Walidacja DPIA/DPA pod kątem wymaganych sekcji         |
# +-------------------------------------------------------------+

"""
PL: Sprawdza, czy w `docs/compliance/dpia.md` oraz `docs/legal/DPA.md` znajdują się
    kluczowe sekcje/zwroty. Raport zapisuje do `out/dpia_report.json` i tworzy
    `out/dpia_ok.txt` gdy wymagane elementy są obecne.

EN: Validates that `docs/compliance/dpia.md` and `docs/legal/DPA.md` contain key
    sections/phrases. Writes `out/dpia_report.json` and creates `out/dpia_ok.txt`
    when all required elements are present.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

REQ_DPIA = [
    "Purpose",
    "Lawful basis",
    "Data minimization",
    "Security",
    "Risk mitigation",
]

REQ_DPA = [
    "Parties:",
    "Subject‑matter:",
    "Duration:",
    "Nature and purpose:",
    "Categories of data:",
    "Sub‑processors:",
    "Security measures:",
    "Data subject rights:",
    "International transfers:",
]


def _scan(path: Path, req: list[str]) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    found = {k: (k in text) for k in req}
    missing = [k for k, v in found.items() if not v]
    return {"path": str(path), "missing": missing, "ok": not missing}


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)
    dpia_p = repo / "docs" / "compliance" / "dpia.md"
    dpa_p = repo / "docs" / "legal" / "DPA.md"
    rep = {
        "dpia": _scan(dpia_p, REQ_DPIA),
        "dpa": _scan(dpa_p, REQ_DPA),
    }
    (out / "dpia_report.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    if rep["dpia"]["ok"] and rep["dpa"]["ok"]:
        (out / "dpia_ok.txt").write_text("ok", encoding="utf-8")
        return 0
    return 0  # report-only by default


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
