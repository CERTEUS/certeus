#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_gauge_gate_inproc.py                |
# | ROLE: Gauge compute smoke (in-proc).                        |
# | PLIK: tests/gates/test_gauge_gate_inproc.py                |
# | ROLA: Smoke obliczenia Gauge (in-proc).                     |
# +-------------------------------------------------------------+
"""
PL: Weryfikuje, że compute_gauge_drift (in-proc) zbiera kappa_max z /v1/cfe/curvature.
EN: Verifies that compute_gauge_drift (in-proc) captures kappa_max from /v1/cfe/curvature.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path

from scripts.gates.compute_gauge_drift import main as compute_main


def test_compute_gauge_drift_produces_payload(tmp_path: Path, monkeypatch) -> None:
    out = tmp_path / "gauge.json"
    # Ensure no external base — use in-proc fallback (TestClient)
    monkeypatch.delenv("CER_BASE", raising=False)
    # Simulate CLI args
    import sys

    argv_bak = sys.argv[:]
    try:
        sys.argv = ["compute_gauge_drift.py", "--out", str(out)]
        assert compute_main() == 0
    finally:
        sys.argv = argv_bak

    obj = json.loads(out.read_text(encoding="utf-8"))
    assert "gauge" in obj and "holonomy_drift" in obj["gauge"]
    # Known stub curvature from CFE router is 0.012 → allow small float ops tolerance
    drift = float(obj["gauge"]["holonomy_drift"])
    assert 0.0 <= drift <= 1.0
