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

    # Load schemas
    sec_schema_path = repo / "schemas" / "security_pco_v0.1.json"
    dpco_schema_path = repo / "schemas" / "data_pco_v0.1.json"
    mco_schema_path = repo / "schemas" / "model_pco_v0.1.json"

    sec_schema = _load_json(sec_schema_path)
    dpco_schema = _load_json(dpco_schema_path)
    mco_schema = _load_json(mco_schema_path)

    report: dict[str, Any] = {
        "sec": {"ok": False, "errors": []},
        "dpco": {"ok": False, "errors": []},
        "mco": {"ok": False, "errors": []},
    }
    missing: list[str] = []
    if not sec_schema:
        missing.append(sec_schema_path.as_posix())
    if not dpco_schema:
        missing.append(dpco_schema_path.as_posix())
    if not mco_schema:
        missing.append(mco_schema_path.as_posix())
    if missing:
        report["errors"] = [f"missing schema: {p}" for p in missing]
        (out_dir / "pco_validation.json").write_text(
            json.dumps(report, indent=2), encoding="utf-8"
        )
        print("PCO Validation: schema missing:", ", ".join(missing))
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

    v_sec = Draft7Validator(sec_schema)  # type: ignore[call-arg]
    sec_errors = [f"SEC: {e.message}" for e in v_sec.iter_errors(sec)]
    report["sec"]["ok"] = len(sec_errors) == 0
    report["sec"]["errors"] = sec_errors

    # Example DPCO
    dpco = {
        "dataset_hash": "sha256:" + ("0" * 64),
        "lineage": ["io.email.mail_id", "cfe.geodesic_action"],
        "dp_epsilon": 0.5,
        "consent_refs": ["consent://demo"],
    }
    v_dpco = Draft7Validator(dpco_schema)  # type: ignore[call-arg]
    dpco_errors = [f"DPCO: {e.message}" for e in v_dpco.iter_errors(dpco)]
    report["dpco"]["ok"] = len(dpco_errors) == 0
    report["dpco"]["errors"] = dpco_errors

    # Example MCO
    mco = {
        "training": {
            "data_dpco": [dpco],
            "sbom_uri": "file://sbom.json",
            "commit_sha": "deadbee",
        },
        "eval": {"ece": 0.01, "brier": 0.05, "auroc": 0.9},
        "bias_report_uri": "https://example.invalid/report",
    }
    v_mco = Draft7Validator(mco_schema)  # type: ignore[call-arg]
    mco_errors = [f"MCO: {e.message}" for e in v_mco.iter_errors(mco)]
    report["mco"]["ok"] = len(mco_errors) == 0
    report["mco"]["errors"] = mco_errors
    (out_dir / "pco_validation.json").write_text(
        json.dumps(report, indent=2), encoding="utf-8"
    )
    all_ok = bool(report["sec"]["ok"] and report["dpco"]["ok"] and report["mco"]["ok"])
    print("PCO Validation:", "OK" if all_ok else "FAIL")
    return 0 if all_ok else 1


# === I/O / ENDPOINTS ===


# === TESTY / TESTS ===


if __name__ == "__main__":
    raise SystemExit(main())
