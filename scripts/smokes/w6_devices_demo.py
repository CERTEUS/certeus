#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w6_devices_demo.py                     |
# | ROLE: Week 6 demo — Devices (HDE/Q-Oracle/Entangle/Chrono)  |
# | PLIK: scripts/smokes/w6_devices_demo.py                     |
# | ROLA: Demo Tygodnia 6 — Devices (HDE/Q-Oracle/Entangle/Chrono) |
# +-------------------------------------------------------------+
"""
PL: Demo W6 — urządzenia: HDE plan, Q-Oracle expectation, Entangle, Chronosync reconcile.
EN: Week-6 demo — devices: HDE plan, Q-Oracle expectation, Entangle, Chronosync reconcile.
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

    r_hde = c.post('/v1/devices/horizon_drive/plan', json={'case': 'w6-hde', 'target_horizon': 0.2})
    r_hde.raise_for_status()
    r_qo = c.post(
        '/v1/devices/qoracle/expectation', json={'question': 'maximize fairness', 'constraints': {'risk': 0.6}}
    )
    r_qo.raise_for_status()
    r_ei = c.post('/v1/devices/entangle', json={'variables': ['A', 'B', 'C', 'D'], 'target_negativity': 0.12})
    r_ei.raise_for_status()
    r_cs = c.post('/v1/devices/chronosync/reconcile', json={'coords': {'case': 'w6-cs', 't': 0}})
    r_cs.raise_for_status()

    _pp('HDE plan', r_hde.json())
    _pp('Q-Oracle', r_qo.json())
    _pp('Entangler', r_ei.json())
    _pp('Chronosync', r_cs.json())

    print("\nOK: Week-6 devices demo complete")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
