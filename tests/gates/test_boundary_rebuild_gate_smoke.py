#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_boundary_rebuild_gate_smoke.py     |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_boundary_rebuild_gate_smoke.py     |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Smoke test dla bramki Boundary-Rebuild (delta_bits==0 i mapa zerowa).

EN: Smoke test for Boundary-Rebuild gate (delta_bits==0 and zero map).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
import subprocess


def test_boundary_gate_ok_with_zero_report(tmp_path: Path) -> None:
    out = tmp_path / "boundary_report.json"
    out.write_text(json.dumps({"boundary": {"delta_bits": 0, "bits_delta_map": {}}}), encoding="utf-8")

    proc = subprocess.run(
        ["python", "scripts/gates/boundary_rebuild_gate.py", "--must-zero", "--report", str(out)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_boundary_gate_fail_on_nonzero(tmp_path: Path) -> None:
    out = tmp_path / "boundary_report.json"
    out.write_text(json.dumps({"boundary": {"delta_bits": 2, "bits_delta_map": {"shard-0": 2}}}), encoding="utf-8")

    proc = subprocess.run(
        ["python", "scripts/gates/boundary_rebuild_gate.py", "--must-zero", "--report", str(out)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1, proc.stdout + proc.stderr


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
