from __future__ import annotations

import os
from pathlib import Path
import subprocess


def run_gate(env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    e = os.environ.copy()
    e.update(env)
    return subprocess.run(
        ["python", "scripts/gates/security_bunker_gate.py"],
        text=True,
        capture_output=True,
        env=e,
    )


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
