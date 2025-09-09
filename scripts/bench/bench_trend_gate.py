#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/bench/bench_trend_gate.py                    |
# | ROLE: Compare current bench vs baseline (report-only)        |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path


def _read_json(p: Path) -> dict:
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {}


def main() -> int:
    cur = _read_json(Path("out/bench.json"))
    prev_path = Path("out/prev_bench.json")
    if not prev_path.exists():
        # common location used by ci-gates after fetching ci-status
        prev_path = Path("ci/bench.json")
    prev = _read_json(prev_path)

    cur_p95 = float(cur.get("worst_p95_ms") or 0.0)
    prev_p95 = float(prev.get("worst_p95_ms") or 0.0)
    delta = None
    if prev_p95 > 0:
        delta = cur_p95 - prev_p95
    lines = []
    lines.append(f"bench: current worst_p95_ms={cur_p95}")
    if prev_p95 > 0:
        lines.append(f"bench: prev worst_p95_ms={prev_p95} (Δ={delta:+.2f} ms)")
    else:
        lines.append("bench: no baseline")

    out = Path("out/bench_trend.txt")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")

    # report-only gate: never fail build, but emit a small summary
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
