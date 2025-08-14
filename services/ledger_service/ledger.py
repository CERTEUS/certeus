# services/ledger_service/ledger.py
from __future__ import annotations

import hashlib
import time
from typing import TypedDict, Dict, List


class LedgerEntry(TypedDict):
    """EN: Single ledger entry. | PL: Pojedynczy wpis w księdze."""

    id: str
    ts: float
    hash: str


def _h(b: bytes) -> str:
    """EN: SHA-256 hex digest. | PL: Suma SHA-256 w hex."""
    return hashlib.sha256(b).hexdigest()


def make_entry(payload: bytes) -> LedgerEntry:
    """
    EN: Create a deterministic entry for given payload.
    PL: Utwórz deterministyczny wpis na podstawie payloadu.
    """
    ts: float = time.time()
    entry_id: str = _h(f"{ts}".encode("utf-8"))
    return LedgerEntry(id=entry_id, ts=ts, hash=_h(payload))


def snapshot(entries: List[LedgerEntry]) -> Dict[str, LedgerEntry]:
    """
    EN: Build an index (id -> entry).
    PL: Zbuduj indeks (id -> wpis).
    """
    out: Dict[str, LedgerEntry] = {}
    for e in entries:
        out[e["id"]] = e
    return out


def latest(entries: List[LedgerEntry]) -> LedgerEntry | None:
    """
    EN: Get the newest entry (max ts) or None if empty.
    PL: Zwróć najnowszy wpis (max ts) albo None jeśli brak.
    """
    if not entries:
        return None
    return max(entries, key=lambda e: e["ts"])
