#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w8_lexenith_demo.py                   |
# | ROLE: Week 8 LEXENITH demo.                                 |
# | PLIK: scripts/smokes/w8_lexenith_demo.py                   |
# | ROLA: Demo tyg. 8 LEXENITH.                                 |
# +-------------------------------------------------------------+
"""
PL: Demo W8 — LEXENITH: motion generate, CLDF renormalize, Why‑Not export, micro_court lock/publish.
EN: Week‑8 demo — LEXENITH: motion generate, CLDF renormalize, Why‑Not export, micro_court lock/publish.
"""

from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    out = Path("reports/w8_lexenith_demo.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    c = TestClient(app)
    cid = "LEX-DEMO-001"
    r_lock = c.post("/v1/lexenith/micro_court/lock", json={"case_id": cid})
    r_pub = c.post("/v1/lexenith/micro_court/publish", json={"case_id": cid})
    r_mot = c.post(
        "/v1/lexenith/motion/generate",
        json={
            "case_id": cid,
            "pattern_id": "motion-dismiss",
            "facts": {"ok": True},
            "citations": ["K 2001", "III 2020"],
        },
    )
    r_cldf = c.post(
        "/v1/lexenith/cldf/renormalize",
        json={"citations": [{"text": "K 2001", "weight": 1.0}, {"text": "III 2020", "weight": 0.5}], "damping": 0.9},
    )
    r_wn = c.post(
        "/v1/lexenith/why_not/export",
        json={"claim": "A", "counter_arguments": ["B", "C"]},
    )
    data = {
        "lock": r_lock.json() if r_lock.status_code == 200 else {"status": r_lock.status_code},
        "publish": r_pub.json() if r_pub.status_code == 200 else {"status": r_pub.status_code},
        "motion": r_mot.json() if r_mot.status_code == 200 else {"status": r_mot.status_code},
        "cldf": r_cldf.json() if r_cldf.status_code == 200 else {"status": r_cldf.status_code},
        "why_not": r_wn.json() if r_wn.status_code == 200 else {"status": r_wn.status_code},
    }
    out.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Saved {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
