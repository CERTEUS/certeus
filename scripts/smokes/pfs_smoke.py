#!/usr/bin/env python3
"""
PL: Smoke ProofFS: inspect i case, zapis do out/.
EN: ProofFS smoke: inspect and case, writes to out/.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import requests as rq


def main() -> int:
    base = os.getenv("CER_BASE", "http://127.0.0.1:8000").rstrip("/")
    out = Path("out")
    out.mkdir(parents=True, exist_ok=True)

    r_ins = rq.get(base + "/v1/pfs/inspect", timeout=3)
    r_ins.raise_for_status()
    (out / "pfs_inspect.json").write_text(json.dumps(r_ins.json(), indent=2), encoding="utf-8")

    cases = r_ins.json().get("cases") or []
    if cases:
        case = cases[0]
        r_case = rq.get(base + f"/v1/pfs/case/{case}", timeout=3)
        r_case.raise_for_status()
        (out / "pfs_case.json").write_text(json.dumps(r_case.json(), indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
