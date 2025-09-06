#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w4_sequence_compare_demo.py           |
# | ROLE: Project script.                                       |
# | PLIK: scripts/smokes/w4_sequence_compare_demo.py           |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: Demo porównania sekwencji (L,T vs T,L) — zapisuje raport ΔUB i liczniki werdyktów.
EN: Sequence compare demo (L,T vs T,L) — saves ΔUB and verdict counts.
"""

from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def _cnt(steps: list[dict]) -> dict[str, int]:
    m = {"ALLOW": 0, "DENY": 0, "ABSTAIN": 0}
    for s in steps:
        v = str(s.get("verdict") or "").upper()
        if v in m:
            m[v] += 1
    return m


def main() -> int:
    out = Path("reports/w4_sequence_compare.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    c = TestClient(app)
    ra = c.post(
        "/v1/qtm/measure_sequence", json={"operators": ["L", "T"], "case": "W4-CMP"}
    )
    rb = c.post(
        "/v1/qtm/measure_sequence", json={"operators": ["T", "L"], "case": "W4-CMP"}
    )
    da = ra.json() if ra.status_code == 200 else {"steps": []}
    db = rb.json() if rb.status_code == 200 else {"steps": []}
    uba = float(((da.get("uncertainty_bound") or {}).get("L_T")) or 0.0)
    ubb = float(((db.get("uncertainty_bound") or {}).get("L_T")) or 0.0)
    rep = {
        "status": {"A": ra.status_code, "B": rb.status_code},
        "delta_ub": round(uba - ubb, 6),
        "counts": {"A": _cnt(da.get("steps") or []), "B": _cnt(db.get("steps") or [])},
    }
    out.write_text(json.dumps(rep, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Saved {out}")
    return 0 if ra.status_code == 200 and rb.status_code == 200 else 1


if __name__ == "__main__":
    raise SystemExit(main())
