#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w4_sequence_demo.py                    |
# | ROLE: Project script.                                       |
# | PLIK: scripts/smokes/w4_sequence_demo.py                    |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: Demo W4 — uruchamia qtm.measure_sequence i zapisuje wynik/headers.
EN: W4 demo — runs qtm.measure_sequence and saves result/headers.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

from fastapi.testclient import TestClient

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402


def main() -> int:
    from services.api_gateway.main import app

    out = Path("reports/w4_sequence.json")
    out.parent.mkdir(parents=True, exist_ok=True)

    client = TestClient(app)
    r = client.post(
        "/v1/qtm/measure_sequence",
        json={"operators": ["L", "T", "W"], "case": "LEX-QTMP-DEMO"},
    )
    body = {}
    try:
        body = r.json()
    except Exception:
        body = {"error": "invalid-json"}
    data = {
        "status": r.status_code,
        "headers": dict(r.headers.items()),
        "body": body,
    }
    out.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Saved {out}")
    return 0 if r.status_code == 200 else 1


if __name__ == "__main__":
    raise SystemExit(main())
