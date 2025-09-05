#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/pco_validation_gate.py                 |
# | ROLE: CI Gate script.                                        |
# | PLIK: scripts/gates/pco_validation_gate.py                 |
# | ROLA: Skrypt bramki CI.                                      |
# +-------------------------------------------------------------+

"""
PL: Bramka PCO Validation (report-only). Weryfikuje przykładowe rozszerzenia
SEC‑PCO względem schematu `schemas/security_pco_v0.1.json` i zapisuje raport
do `out/pco_validation.json`. Zwraca kod ≠0 przy naruszeniach.

EN: PCO Validation Gate (report-only). Validates example SEC‑PCO extension
against `schemas/security_pco_v0.1.json` and writes a report to
`out/pco_validation.json`. Returns non-zero on violations.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from jsonschema import Draft7Validator

# === KONFIGURACJA / CONFIGURATION ===


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def _load_json(path: Path) -> dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}


# === LOGIKA / LOGIC ===


def main() -> int:
    repo = _repo_root()
    out_dir = repo / "out"
    out_dir.mkdir(parents=True, exist_ok=True)

    # Load SEC‑PCO schema
    sec_schema_path = repo / "schemas" / "security_pco_v0.1.json"
    sec_schema = _load_json(sec_schema_path)
    if not sec_schema:
        report = {"ok": False, "errors": [f"missing schema: {sec_schema_path.as_posix()}"]}
        (out_dir / "pco_validation.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
        print("PCO Validation: schema missing")
        return 1

    # Example SEC‑PCO object (minimal valid)
    sec = {
        "finding_id": "SEC-0001",
        "severity": "HIGH",
        "status": "OPEN",
        "controls": ["ISO27001:A.12.6"],
        "evidence": [
            {
                "digest": "sha256:" + ("a" * 64),
                "type": "artifact",
                "uri": "pfs://mail/MSEC/rep.pdf",
            }
        ],
        "cwe": ["CWE-79"],
        "cve": ["CVE-2025-0001"],
        "cvss": 8.2,
    }

    v = Draft7Validator(sec_schema)  # type: ignore[call-arg]
    errors = [f"SEC schema: {e.message}" for e in v.iter_errors(sec)]
    ok = len(errors) == 0
    report = {"ok": ok, "errors": errors}
    (out_dir / "pco_validation.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print("PCO Validation:", "OK" if ok else "FAIL")
    return 0 if ok else 1


# === I/O / ENDPOINTS ===


# === TESTY / TESTS ===


if __name__ == "__main__":
    raise SystemExit(main())
