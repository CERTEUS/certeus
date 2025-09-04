#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w5_operator_composer_demo.py           |
# | ROLE: Week 5 demo — Operator Composer / Presets             |
# | PLIK: scripts/smokes/w5_operator_composer_demo.py           |
# | ROLA: Demo Tygodnia 5 — Operator Composer / Presets         |
# +-------------------------------------------------------------+
"""
PL: Demo W5 — Operator Composer: zapis presetu operatora dla sprawy
    i weryfikacja, że pomiar używa presetu (operator w PCO header).

EN: Week-5 demo — Operator Composer: save operator preset for a case
    and verify measure uses the preset (operator in PCO header).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json


def _ensure_repo_on_path() -> None:
    from pathlib import Path as _P
    import sys as _sys

    _sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402


_ensure_repo_on_path()

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app as gateway_app  # noqa: E402


def _pp(title: str, data) -> None:
    print(f"\n== {title} ==")
    try:
        print(json.dumps(data, indent=2, ensure_ascii=False))
    except Exception:
        print(str(data))


def main() -> int:
    c = TestClient(gateway_app)
    case_id = "LEX-OP-001"

    # Save preset: prefer operator T for this case
    r_p = c.post("/v1/qtm/preset", json={"case": case_id, "operator": "T"})
    r_p.raise_for_status()
    _pp("preset saved", r_p.json())

    # Measure providing another operator, but 'source' binds to case -> preset overrides
    r_m = c.post("/v1/qtm/measure", json={"operator": "L", "source": case_id})
    r_m.raise_for_status()
    header = r_m.headers.get("X-CERTEUS-PCO-qtm.collapse_event") or "{}"
    _pp("measure", {"header": header, "body": r_m.json()})
    assert '"operator":"T"' in header, "Expected operator T enforced by preset"
    print("\nOK: Operator Composer demo complete (preset enforced)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
