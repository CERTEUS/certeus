#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w5_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w5_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W5 — lexqft v0.1 i Path‑Coverage: tunelowanie (2 scenariusze),
    coverage/update + gate threshold, porównanie z QTMP (sequence).

EN: W5 — lexqft v0.1 & Path‑Coverage: tunneling (2 scenarios),
    coverage/update + gate, comparison with QTMP (sequence).
"""

from __future__ import annotations

import json
from pathlib import Path, Path as _P
import subprocess
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    c = TestClient(app)
    # Tunneling: low vs high energy
    low = c.post(
        "/v1/lexqft/tunnel", json={"evidence_energy": 0.2, "state_uri": "psi://w5-low"}
    )
    high = c.post(
        "/v1/lexqft/tunnel", json={"evidence_energy": 1.2, "state_uri": "psi://w5-high"}
    )
    # Coverage: set weighted items to exceed threshold
    c.post("/v1/lexqft/coverage/reset")
    items = [
        {"gamma": 0.95, "weight": 2.0, "uncaptured": 0.05},
        {"gamma": 0.90, "weight": 1.0, "uncaptured": 0.08},
    ]
    c.post("/v1/lexqft/coverage/update", json=items)
    cov = c.get("/v1/lexqft/coverage/state").json()
    # Gate: run path_coverage_gate against this state
    tmp = Path("out")
    tmp.mkdir(parents=True, exist_ok=True)
    covf = tmp / "path_cov_demo.json"
    cov_payload = {
        "coverage": {
            "coverage_gamma": cov.get("coverage_gamma"),
            "uncaptured_mass": cov.get("uncaptured_mass"),
        }
    }
    covf.write_text(json.dumps(cov_payload), encoding="utf-8")
    gate = subprocess.run(
        [
            "python",
            "scripts/gates/path_coverage_gate.py",
            "--min-gamma",
            "0.90",
            "--max-uncaptured",
            "0.10",
            "--input",
            str(covf),
        ],
        capture_output=True,
        text=True,
    )
    # QTMP: run a short sequence
    case = "LEX-W5-QTMP"
    c.post(
        "/v1/qtm/init_case", json={"case": case, "basis": ["ALLOW", "DENY", "ABSTAIN"]}
    )
    seq = c.post(
        "/v1/qtm/measure_sequence", json={"operators": ["L", "T", "W"], "case": case}
    ).json()
    rep = {
        "tunnel_low": low.json() if low.status_code == 200 else None,
        "tunnel_high": high.json() if high.status_code == 200 else None,
        "coverage_state": cov,
        "path_gate": {"rc": gate.returncode, "out": (gate.stdout or "").strip()},
        "qtm_seq": seq,
    }
    Path("reports").mkdir(parents=True, exist_ok=True)
    Path("reports/w5_demo.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print(json.dumps({"ok": gate.returncode == 0, "gamma": cov.get("coverage_gamma")}))
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
