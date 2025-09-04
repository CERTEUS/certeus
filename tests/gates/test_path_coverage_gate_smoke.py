#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_path_coverage_gate_smoke.py        |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_path_coverage_gate_smoke.py        |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Smoke test dla Path‑Coverage Gate: przygotuj plik z metrykami i uruchom
    gate z progami (pass/fail).

EN: Smoke test for Path‑Coverage Gate: prepare metrics file and run the gate
    with thresholds (pass/fail).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
import subprocess


def test_path_coverage_gate_ok_and_fail(tmp_path: Path) -> None:
    metrics_ok = {"coverage": {"coverage_gamma": 0.95, "uncaptured_mass": 0.02}}
    p_ok = tmp_path / "cov_ok.json"
    p_ok.write_text(json.dumps(metrics_ok), encoding="utf-8")

    metrics_bad = {"coverage": {"coverage_gamma": 0.80, "uncaptured_mass": 0.20}}
    p_bad = tmp_path / "cov_bad.json"
    p_bad.write_text(json.dumps(metrics_bad), encoding="utf-8")

    # OK when gamma >= 0.90 and uncaptured <= 0.10
    pr_ok = subprocess.run(
        [
            "python",
            "scripts/gates/path_coverage_gate.py",
            "--min-gamma",
            "0.90",
            "--max-uncaptured",
            "0.10",
            "--input",
            str(p_ok),
        ],
        capture_output=True,
        text=True,
    )
    assert pr_ok.returncode == 0, pr_ok.stdout + pr_ok.stderr

    # FAIL when gamma < 0.90 or uncaptured > 0.10
    pr_fail = subprocess.run(
        [
            "python",
            "scripts/gates/path_coverage_gate.py",
            "--min-gamma",
            "0.90",
            "--max-uncaptured",
            "0.10",
            "--input",
            str(p_bad),
        ],
        capture_output=True,
        text=True,
    )
    assert pr_fail.returncode == 1, pr_fail.stdout + pr_fail.stderr


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
