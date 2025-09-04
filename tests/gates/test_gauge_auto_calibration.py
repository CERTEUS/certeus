#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_gauge_auto_calibration.py          |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_gauge_auto_calibration.py          |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Test auto‑kalibracji ε dla Gauge‑Gate: compute_gauge_drift → compute_gauge_epsilon → gate OK.

EN: Auto‑calibration test for Gauge‑Gate: compute_gauge_drift → compute_gauge_epsilon → gate OK.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
import subprocess


def test_auto_epsilon_makes_gate_pass(tmp_path: Path) -> None:
    # 1) compute drift
    drift_path = tmp_path / "gauge.json"
    rc1 = subprocess.run(
        ["python", "scripts/gates/compute_gauge_drift.py", "--out", str(drift_path)],
        capture_output=True,
        text=True,
    )
    assert rc1.returncode == 0, rc1.stdout + rc1.stderr
    drift_data = json.loads(drift_path.read_text(encoding="utf-8"))
    drift = float(((drift_data or {}).get("gauge") or {}).get("holonomy_drift", 0.0))

    # 2) compute epsilon from drift + components
    eps_path = tmp_path / "epsilon.json"
    rc2 = subprocess.run(
        [
            "python",
            "scripts/gates/compute_gauge_epsilon.py",
            "--input",
            str(drift_path),
            "--out",
            str(eps_path),
        ],
        capture_output=True,
        text=True,
    )
    assert rc2.returncode == 0, rc2.stdout + rc2.stderr
    eps_data = json.loads(eps_path.read_text(encoding="utf-8"))
    eps = float(((eps_data or {}).get("gauge") or {}).get("epsilon", 0.0))
    assert eps >= drift

    # 3) gate should pass with computed epsilon
    rc3 = subprocess.run(
        [
            "python",
            "scripts/gates/gauge_gate.py",
            "--epsilon",
            f"{eps}",
            "--input",
            str(drift_path),
        ],
        capture_output=True,
        text=True,
    )
    assert rc3.returncode == 0, rc3.stdout + rc3.stderr


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

