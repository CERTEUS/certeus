#!/usr/bin/env python3
"""
PL: Prosty magazyn idempotencyjny in‑proc (MVP) dla POST (Devices).
EN: Simple in‑proc idempotency store (MVP) for POST (Devices).
"""

from __future__ import annotations

from dataclasses import dataclass
import time
from typing import Any, Dict, Optional


@dataclass(slots=True)
class IdemEntry:
    created: float
    payload: Dict[str, Any]


_STORE: dict[str, IdemEntry] = {}
_TTL_SEC: float = 15 * 60.0  # 15 min cache (MVP)


def get(key: Optional[str]) -> Optional[Dict[str, Any]]:
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


def put(key: Optional[str], payload: Dict[str, Any]) -> None:
    if not key:
        return
    _STORE[key] = IdemEntry(created=time.time(), payload=dict(payload))

