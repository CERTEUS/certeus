#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_auto_calibrate_omega.py            |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_auto_calibrate_omega.py            |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy auto‑kalibracji Ω‑Kernel na małym korpusie par.
EN: Ω‑Kernel auto‑calibration tests on a small pair corpus.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys


def _write_pairs(p: Path, lines: list[str]) -> Path:
    p.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return p


def test_auto_calibrate_emits_thresholds_and_stats(tmp_path: Path) -> None:
    pairs = tmp_path / "pairs_sec.txt"
    _write_pairs(
        pairs,
        [
            "Exploit i patch zwiększają krytycznosc ||| Eksploit i łatka obniżają poważność",
            "Poważność podatność z CVE i wektor atak wg CVSS ||| Poważność podatność z CVE i wektor atak wg CVSS",
        ],
    )
    out = tmp_path / "calib.json"
    rc = subprocess.run(
        [
            sys.executable,
            "scripts/gates/auto_calibrate_omega.py",
            "--pairs",
            str(pairs),
            "--out",
            str(out),
            "--domain",
            "sec",
        ],
        capture_output=True,
        text=True,
    ).returncode
    assert rc == 0 and out.exists()
    data = json.loads(out.read_text(encoding="utf-8"))
    assert "thresholds" in data and "stats" in data
    assert "omega" in data["thresholds"]
    assert "omega" in data["stats"]
    om = data["thresholds"]["omega"]
    assert {"jaccard_max", "entropy_max", "entity_jaccard_max"}.issubset(om.keys())
    assert 0.0 <= om["jaccard_max"] <= 1.0
    # mapped present with correct domain
    assert "omega_mapped" in data["thresholds"]
    assert data["thresholds"]["omega_mapped"]["domain"] == "sec"
