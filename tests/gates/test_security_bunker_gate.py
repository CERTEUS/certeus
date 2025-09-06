"""
PL: Testy jednostkowe bramki Bunkra: tryb off, atest OK oraz brak atestu.
EN: Unit tests for Bunker gate: off mode, attested OK and missing attestation.
"""

from __future__ import annotations

import os  # noqa: E402
from pathlib import Path  # noqa: E402
import subprocess  # noqa: E402
import sys  # noqa: E402

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_security_bunker_gate.py             |
# | ROLE: Tests for Security Bunker gate                        |
# | PLIK: tests/gates/test_security_bunker_gate.py             |
# | ROLA: Testy bramki Security Bunker                          |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===

# === LOGIKA / LOGIC ===


def run_gate(env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    e = os.environ.copy()
    e.update(env)
    # Add current directory to PYTHONPATH for module imports
    current_path = e.get("PYTHONPATH", "")
    if current_path:
        e["PYTHONPATH"] = f"{Path.cwd()}:{current_path}"
    else:
        e["PYTHONPATH"] = str(Path.cwd())
    return subprocess.run(
        [sys.executable, "scripts/gates/security_bunker_gate.py"],
        text=True,
        capture_output=True,
        env=e,
        cwd=Path.cwd(),  # Ensure proper working directory
    )


# === TESTY / TESTS ===


def test_bunker_off_ok() -> None:
    res = run_gate({"BUNKER": "0", "PROOFGATE_BUNKER": "0"})
    assert res.returncode == 0, res.stderr or res.stdout
    assert "BUNKER=off" in (res.stdout + res.stderr)


def test_bunker_on_with_attestation_ok() -> None:
    att = Path("security/bunker/attestation.json").resolve()
    assert att.exists()
    res = run_gate(
        {
            "BUNKER": "1",
            "BUNKER_ATTESTATION_PATH": str(att),
        }
    )
    assert res.returncode == 0, res.stderr or res.stdout
    assert "attested" in (res.stdout + res.stderr)


def test_bunker_on_missing_attestation_fail() -> None:
    missing = Path("tmp/nonexistent/does_not_exist.json").resolve()
    res = run_gate(
        {
            "BUNKER": "1",
            "BUNKER_ATTESTATION_PATH": str(missing),
        }
    )
    assert res.returncode != 0
    assert "not attested" in (res.stdout + res.stderr)
