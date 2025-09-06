#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_gauge_gate_with_telemetry.py       |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_gauge_gate_with_telemetry.py       |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Gauge Gate z realną telemetrią CFE (kappa_max). compute_gauge_drift → gate.

EN: Gauge Gate using real CFE telemetry (kappa_max). compute_gauge_drift → gate.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
import subprocess


def test_gauge_gate_ok_and_fail(tmp_path: Path) -> None:
    # compute-gauge writes kappa_max drift to JSON
    out = tmp_path / "gauge.json"
    proc_c = subprocess.run(
        ["python", "scripts/gates/compute_gauge_drift.py", "--out", str(out)],
        capture_output=True,
        text=True,
    )
    assert proc_c.returncode == 0
    data = json.loads(out.read_text(encoding="utf-8"))
    drift = float(((data or {}).get("gauge") or {}).get("holonomy_drift", 0.0))
    assert drift >= 0.0

    # OK when epsilon >= drift
    proc_ok = subprocess.run(
        [
            "python",
            "scripts/gates/gauge_gate.py",
            "--epsilon",
            f"{drift + 0.01}",
            "--input",
            str(out),
        ],
        capture_output=True,
        text=True,
    )
    assert proc_ok.returncode == 0, proc_ok.stdout + proc_ok.stderr

    # FAIL when epsilon < drift
    bad_eps = max(0.0, drift - 0.0001)
    proc_fail = subprocess.run(
        [
            "python",
            "scripts/gates/gauge_gate.py",
            "--epsilon",
            f"{bad_eps}",
            "--input",
            str(out),
        ],
        capture_output=True,
        text=True,
    )
    # If drift==0, bad_eps==0 -> still OK; accept either outcome deterministically by bumping
    if drift == 0.0:
        assert proc_fail.returncode == 0
    else:
        assert proc_fail.returncode == 1


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
