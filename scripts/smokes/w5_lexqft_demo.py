#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w5_lexqft_demo.py                      |
# | ROLE: Week 5 demo — LexQFT tunnel + coverage                |
# | PLIK: scripts/smokes/w5_lexqft_demo.py                      |
# | ROLA: Demo Tygodnia 5 — LexQFT tunnel + coverage            |
# +-------------------------------------------------------------+
"""
PL: Demo W5 — LexQFT: dwa scenariusze tunelowania (niska vs wysoka energia)
    i podsumowanie pokrycia ścieżek.

EN: Week-5 demo — LexQFT: two tunneling scenarios (low vs high energy)
    and path coverage summary.
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
    # Low energy: expect reflection / lower p_tunnel
    r_low = c.post('/v1/lexqft/tunnel', json={'evidence_energy': 0.6})
    r_low.raise_for_status()
    _pp('Tunnel (low energy)', r_low.json())
    # High energy: expect p_tunnel ~ 0.95
    r_high = c.post('/v1/lexqft/tunnel', json={'evidence_energy': 1.2})
    r_high.raise_for_status()
    _pp('Tunnel (high energy)', r_high.json())
    # Coverage snapshot
    r_cov = c.get('/v1/lexqft/coverage')
    r_cov.raise_for_status()
    _pp('Coverage', r_cov.json())
    print('\nOK: Week-5 demo complete (LexQFT tunnel + coverage)')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
