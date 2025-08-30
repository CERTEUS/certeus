# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/truth/test_solvers.py             |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                    CERTEUS - Truth Tests                    |
# +-------------------------------------------------------------+
# | PLIK / FILE: tests/truth/test_solvers.py                    |
# | ROLA / ROLE:                                                |
# |  PL: Testy jądra prawdy i generatora artefaktów dowodowych. |
# |  EN: Tests for the truth kernel and proof artifact generator.|
# +-------------------------------------------------------------+

"""
PL: Ten moduł zawiera testy dla generatora dowodów:
    - Test jednostkowy: bezpośrednie wywołanie generate_proofs(...)
    - Test CLI (opcjonalny): wywołanie skryptu przez subprocess, jeśli dostępny jest `uv`.

EN: This module contains tests for the proof generator:
    - Unit test: direct call to generate_proofs(...)
    - Optional CLI test: run the script via subprocess if `uv` is available.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Literal

import pytest

# Import bezpośrednio z modułu – stabilniej niż subprocess
# Direct import from module – more stable than subprocess
from scripts.generate_proofs import generate_proofs


@pytest.mark.parametrize(
    "formats,mode,expected_files",
    [
        (["drat", "lfsc"], "stub", ["z3.drat", "cvc5.lfsc"]),
        (["drat"], "simulate", ["z3.drat"]),
        (["lfsc"], "simulate", ["cvc5.lfsc"]),
    ],
)
def test_generate_proofs_function_creates_expected_artifacts(
    formats: list[str],
    mode: Literal["stub", "simulate"],
    expected_files: list[str],
) -> None:
    """
    PL: Sprawdza, czy generate_proofs(...) tworzy oczekiwane pliki w danym trybie i formatach.
    EN: Verifies that generate_proofs(...) creates expected files for given mode and formats.
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        out: Path = Path(tmpdir)
        # Wywołanie funkcji bezpośrednio (unit)
        generate_proofs(out, formats, mode)

        # Weryfikacja istnienia plików
        for name in expected_files:
            name_str: str = name
            p: Path = out / name_str
            assert p.exists(), f"PL: Brak pliku: {p} | EN: Missing file: {p}"

        # W trybie simulate sprawdź, że pliki nie są puste
        if mode == "simulate":
            for name in expected_files:
                p: Path = out / name
                size: int = p.stat().st_size
                assert size > 0, f"PL: Pusty plik: {p} | EN: Empty file: {p}"


@pytest.mark.skipif(shutil.which("uv") is None, reason="uv not available on PATH")
def test_generate_proofs_cli_smoke_test() -> None:
    """
    PL: „Dymny” test CLI – uruchamia skrypt przez `uv run python ...` i sprawdza wyjście.
    EN: CLI smoke test – runs the script via `uv run python ...` and checks output.
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        out: Path = Path(tmpdir)
        cmd: list[str] = [
            "uv",
            "run",
            "--no-sync",
            sys.executable,  # aktywny Python z venv
            "scripts/generate_proofs.py",
            "--out",
            str(out),
            "--mode",
            "simulate",
        ]
        res = subprocess.run(cmd, check=True, capture_output=True, text=True)
        stdout: str = res.stdout

        assert ("Created simulated proof with content" in stdout) or ("Created stub proof" in stdout)
        assert (out / "z3.drat").exists()
        assert (out / "cvc5.lfsc").exists()
