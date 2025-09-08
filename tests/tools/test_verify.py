#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# +-------------------------------------------------------------+
# | FILE: tests/tools/test_verify.py                            |
# | ROLE: Smoke test for PCO verify CLI                        |
# +-------------------------------------------------------------+

from pathlib import Path
import subprocess


def test_verify_hello_ok():
    repo_root = Path(__file__).resolve().parents[2]
    pco = repo_root / "examples" / "pco" / "hello.json"
    cli = repo_root / "tools" / "pco" / "verify.py"
    assert pco.exists()
    out = subprocess.run(["python3", str(cli), str(pco)], capture_output=True, text=True, check=True)
    assert "PCO: OK" in out.stdout
