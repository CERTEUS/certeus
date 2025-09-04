#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w6_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w6_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W6 — Devices v0.1: HDE plan, Q‑Oracle expectation, Entangler, Chronosync.

EN: W6 — Devices v0.1: HDE plan, Q‑Oracle expectation, Entangler, Chronosync.
"""

from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    c = TestClient(app)
    hde = c.post('/v1/devices/horizon_drive/plan', json={'case': 'DEV-6', 'target_horizon': 0.25}).json()
    qo = c.post('/v1/devices/qoracle/expectation', json={'question': 'Should we appeal?'}).json()
    ent = c.post('/v1/devices/entangle', json={'variables': ['X', 'Y'], 'target_negativity': 0.12}).json()
    chr_ = c.post('/v1/devices/chronosync/reconcile', json={'coords': {'t': 0}, 'pc_delta': {}}).json()
    rep = {'hde': hde, 'qoracle': qo, 'entangle': ent, 'chronosync': chr_}
    Path('reports').mkdir(parents=True, exist_ok=True)
    Path('reports/w6_demo.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
    print(json.dumps({'ok': True, 'hde_cost': hde.get('cost_tokens')}))
    return 0


if __name__ == '__main__':  # pragma: no cover
    raise SystemExit(main())
