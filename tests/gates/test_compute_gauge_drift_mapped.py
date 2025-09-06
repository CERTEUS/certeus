#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_compute_gauge_drift_mapped.py      |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_compute_gauge_drift_mapped.py      |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy trybu domenowego (report-only) w compute_gauge_drift.
EN: Tests for domain (report-only) mode in compute_gauge_drift.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys


def _run(args: list[str], env: dict[str, str] | None = None) -> tuple[int, str, dict]:
    out = Path("out")
    out.mkdir(exist_ok=True)
    rc = subprocess.run(
        [sys.executable, *args], capture_output=True, text=True, env=env
    ).returncode
    data = json.loads((out / "mapped.json").read_text(encoding="utf-8"))
    return rc, "", data


def test_compute_gauge_drift_emits_mapped_metrics(tmp_path: Path) -> None:
    before = tmp_path / "b.txt"
    after = tmp_path / "a.txt"
    before.write_text("Exploit i patch zwiększają krytycznosc", encoding="utf-8")
    after.write_text("Eksploit i łatka obniżają poważność", encoding="utf-8")

    rc, _, data = _run(
        [
            "scripts/gates/compute_gauge_drift.py",
            "--out",
            "out/mapped.json",
            "--before-file",
            str(before),
            "--after-file",
            str(after),
            "--domain",
            "sec",
        ]
    )

    assert rc == 0
    assert "omega_mapped" in data and data["omega_mapped"]["domain"] == "sec"
    assert "jaccard_drift" in data["omega_mapped"]
    # Domain map is substitution-only; token count stays equal
    assert int(data["omega_mapped"]["token_count_delta"]) == 0


def test_mapped_thresholds_report_only(tmp_path: Path) -> None:
    before = tmp_path / "b.txt"
    after = tmp_path / "a.txt"
    before.write_text("Exploit i patch zwiększają krytycznosc", encoding="utf-8")
    after.write_text("Eksploit i łatka obniżają poważność", encoding="utf-8")
    # Set tight threshold but do not enforce; expect rc==0
    args = [
        "scripts/gates/compute_gauge_drift.py",
        "--out",
        "out/mapped.json",
        "--before-file",
        str(before),
        "--after-file",
        str(after),
        "--domain",
        "sec",
        "--max-jaccard-mapped",
        "0.1",
    ]
    rc = subprocess.run(
        [sys.executable, *args], capture_output=True, text=True, env=os.environ
    ).returncode
    assert rc == 0
