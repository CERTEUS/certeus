#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w4_qtmp_demo.py                        |
# | ROLE: Week 4 demo — QTMP (measure, sequence, decoherence)   |
# | PLIK: scripts/smokes/w4_qtmp_demo.py                        |
# | ROLA: Demo Tygodnia 4 — QTMP (pomiar, sekwencja, dekoherencja) |
# +-------------------------------------------------------------+
"""
PL: Demo W4 — QTMP: init_case, measure (L→T vs T→L), dekoherencja i wpisy do Ledger.
EN: Week-4 demo — QTMP: init_case, measure (L→T vs T→L), decoherence and Ledger entries.
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
    case_id = "LEX-001-qtmp"

    r_init = c.post(
        "/v1/qtm/init_case",
        json={"case": case_id, "basis": ["ALLOW", "DENY", "ABSTAIN"]},
    )
    r_init.raise_for_status()
    _pp("init_case", r_init.json())

    # Baseline without decoherence
    r_lt = c.post("/v1/qtm/measure", json={"operator": "LT", "source": case_id})
    r_tl = c.post("/v1/qtm/measure", json={"operator": "TL", "source": case_id})
    r_lt.raise_for_status()
    r_tl.raise_for_status()
    _pp("measure L->T", r_lt.json())
    _pp("measure T->L", r_tl.json())

    # Apply decoherence and re-measure
    c.post(
        "/v1/qtm/decoherence",
        json={"case": case_id, "channel": "dephasing", "gamma": 0.2},
    ).raise_for_status()
    r_lt2 = c.post("/v1/qtm/measure", json={"operator": "LT", "source": case_id})
    r_tl2 = c.post("/v1/qtm/measure", json={"operator": "TL", "source": case_id})
    r_lt2.raise_for_status()
    r_tl2.raise_for_status()
    _pp("measure L->T (decoherence)", r_lt2.json())
    _pp("measure T->L (decoherence)", r_tl2.json())

    # Show ledger entries count
    r_log = c.get(f"/v1/ledger/{case_id}/records")
    r_log.raise_for_status()
    _pp("ledger entries", {"case": case_id, "count": len(r_log.json())})

    print("\nOK: Week-4 demo complete (QTMP: L->T vs T->L + decoherence + ledger)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
