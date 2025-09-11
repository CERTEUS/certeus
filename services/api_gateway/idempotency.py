#!/usr/bin/env python3
# +-------------------------------------------------------------+
# | CERTEUS Control System | ForgeHeader v3 - Enterprise     |
# | FILE: workspaces/certeus/services/api_gateway/idempotency.py                                      |
# | ROLE: Service implementation                                        |
# +-------------------------------------------------------------+

"""
PL: Prosty magazyn idempotencyjny in‑proc (MVP) dla POST (Devices).
EN: Simple in‑proc idempotency store (MVP) for POST (Devices).
"""

from __future__ import annotations

from dataclasses import dataclass
import time
from typing import Any


@dataclass(slots=True)
class IdemEntry:
    created: float
    payload: dict[str, Any]


_STORE: dict[str, IdemEntry] = {}
_TTL_SEC: float = 15 * 60.0  # 15 min cache (MVP)


def get(key: str | None) -> dict[str, Any] | None:
    if not key:
        return None
    it = _STORE.get(key)
    if not it:
        return None
    if (time.time() - it.created) > _TTL_SEC:
        try:
            del _STORE[key]
        except Exception:
            pass
        return None
    return dict(it.payload)


def put(key: str | None, payload: dict[str, Any]) -> None:
    if not key:
        return
    _STORE[key] = IdemEntry(created=time.time(), payload=dict(payload))
