#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_pqcrypto_gate_smoke.py             |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_pqcrypto_gate_smoke.py             |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Smoke test dla PQ‑crypto gate — zapisuje marker do `out/pqcrypto.txt` i
    nie failuje w trybie informacyjnym.

EN: Smoke test for PQ‑crypto gate — writes `out/pqcrypto.txt` marker and does
    not fail in informational mode.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import os
from pathlib import Path
import subprocess


def _run_gate(env: dict[str, str]) -> tuple[int, str]:
    e = os.environ.copy()
    e.update(env)
    proc = subprocess.run(
        ["python", "scripts/gates/pqcrypto_gate.py"],
        capture_output=True,
        text=True,
        env=e,
    )
    return proc.returncode, (proc.stdout or "")


def test_pqcrypto_gate_off_and_ready(tmp_path: Path) -> None:
    # OFF
    rc_off, out_off = _run_gate(
        {"PQCRYPTO_REQUIRE": "0", "PQCRYPTO_READY": "0", "OUT_DIR": str(tmp_path)}
    )
    assert rc_off == 0
    # READY
    rc_ready, out_ready = _run_gate(
        {"PQCRYPTO_REQUIRE": "1", "PQCRYPTO_READY": "1", "OUT_DIR": str(tmp_path)}
    )
    assert rc_ready == 0
    # Marker file
    marker = Path("out") / "pqcrypto.txt"
    assert marker.exists()


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
