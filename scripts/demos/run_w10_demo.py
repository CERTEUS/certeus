#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w10_demo.py                        |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w10_demo.py                        |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W10 — Observability & SRE: pomiar SLO (p95/error-rate) in‑proc + weryfikacja
    progów oraz szybki perf bench. Zapisuje raport `reports/w10_demo.json`.

EN: W10 — Observability & SRE: measure SLO (p95/error-rate) in‑proc + threshold
    check and quick perf bench. Writes `reports/w10_demo.json`.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess


def _run(cmd: list[str], env: dict[str, str] | None = None) -> tuple[int, str, str]:
    e = os.environ.copy()
    if env:
        e.update(env)
    p = subprocess.run(cmd, capture_output=True, text=True, env=e)
    return p.returncode, (p.stdout or ""), (p.stderr or "")


def main() -> int:
    out_dir = Path("reports")
    out_dir.mkdir(parents=True, exist_ok=True)
    out_slo = Path("out")
    out_slo.mkdir(parents=True, exist_ok=True)

    # 1) SLO measure (in-proc)
    _run(
        ["python", "scripts/slo_gate/measure_api.py"],
        env={"SLO_MEASURE_COUNT": "80", "SLO_OUT": str(out_slo / "slo.json")},
    )
    # 2) SLO check (thresholds)
    rc_slo, out_slo_txt, _ = _run(
        ["python", "scripts/slo_gate/check_slo.py"],
        env={"SLO_OUT": str(out_slo / "slo.json"), "SLO_MAX_P95_MS": "300", "SLO_MAX_ERROR_RATE": "0.01"},
    )
    # 3) Quick perf bench (in-proc)
    rc_perf, out_perf, _ = _run(
        [
            "python",
            "scripts/perf/quick_bench.py",
            "--iters",
            "8",
            "--p95-max-ms",
            "300",
            "--out",
            "out/perf_bench.json",
        ]
    )

    rep = {
        "slo_check": {"rc": rc_slo, "out": out_slo_txt.strip()},
        "perf": {"rc": rc_perf, "out": out_perf.strip()},
    }
    (out_dir / "w10_demo.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print(json.dumps({"ok": (rc_slo == 0 and rc_perf == 0)}))
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
