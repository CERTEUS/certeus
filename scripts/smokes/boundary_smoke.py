#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/boundary_smoke.py                      |
# | ROLE: Project script.                                       |
# | PLIK: scripts/smokes/boundary_smoke.py                      |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: Lekki smoke Boundary — pobiera /v1/boundary/status i zapisuje wynik.
EN: Lightweight Boundary smoke — fetches /v1/boundary/status and saves output.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

from fastapi.testclient import TestClient

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

# === KONFIGURACJA / CONFIGURATION ===

OUT = Path("reports/boundary_status.json")

# === LOGIKA / LOGIC ===


def main() -> int:
    from services.api_gateway.main import app

    OUT.parent.mkdir(parents=True, exist_ok=True)
    c = TestClient(app)
    r = c.get("/v1/boundary/status")
    print(f"status={r.status_code}")
    try:
        body = r.json()
    except Exception:
        body = {"error": "invalid-json"}
    OUT.write_text(json.dumps(body, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Saved {OUT}")
    return 0 if r.status_code == 200 else 1


if __name__ == "__main__":
    raise SystemExit(main())
