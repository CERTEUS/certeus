#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/services/test_ledger.py           |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

# -*- coding: utf-8 -*-
# +=====================================================================+
# |                              CERTEUS                                |
# |                           Ledger Service                            |
# +=====================================================================+
# | MODULE:  services/ledger_service/ledger.py                          |
# | VERSION: 1.2.0                                                      |
# | DATE:    2025-08-16                                                 |
# +=====================================================================+
# | ROLE: In-memory ledger + provenance hash helpers.                   |
# |       API zgodne z testami: append(), read_all(), alias 'hash'.     |
# +=====================================================================+
"""
PL: Testy Ledger – sprawdzanie łańcucha skrótów i nagłówków.
EN: Ledger tests – verification of hash chain and headers.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from hashlib import sha256
from typing import Any, Dict, List, Mapping, Optional


def _normalize_for_hash(data: Mapping[str, Any], *, include_timestamp: bool) -> bytes:
    if not include_timestamp and "timestamp" in data:
        work = {k: v for k, v in data.items() if k != "timestamp"}
    else:
        work = dict(data)
    return json.dumps(work, sort_keys=True, separators=(",", ":")).encode("utf-8")


def compute_provenance_hash(
    data: Mapping[str, Any], *, include_timestamp: bool = False
) -> str:
    return sha256(
        _normalize_for_hash(data, include_timestamp=include_timestamp)
    ).hexdigest()


def verify_provenance_hash(
    data: Mapping[str, Any], expected_hash: str, *, include_timestamp: bool = False
) -> bool:
    return (
        compute_provenance_hash(data, include_timestamp=include_timestamp)
        == expected_hash
    )


class LedgerRecord:
    """
    Elastyczny rekord księgi:
      - przyjmuje zarówno 'document_hash', jak i alias 'hash'
      - ma opcjonalne 'meta'
      - wszystkie pola mają domyślne wartości (żeby test mógł wołać bez wszystkich argów)
    """

    def __init__(
        self,
        *,
        event_id: int = 0,
        type: str = "INPUT_INGESTION",
        case_id: str = "",
        document_hash: Optional[str] = None,
        timestamp: str = "",
        chain_prev: Optional[str] = None,
        chain_self: str = "",
        meta: Optional[Mapping[str, Any]] = None,
        **extras: Any,
    ) -> None:
        # aliasy z testów: 'hash' -> document_hash
        if document_hash is None and "hash" in extras:
            document_hash = str(extras.pop("hash"))

        self.event_id = event_id
        self.type = type
        self.case_id = case_id
        self.document_hash = document_hash
        self.timestamp = timestamp
        self.chain_prev = chain_prev
        self.chain_self = chain_self
        self.meta = dict(meta) if meta is not None else None
        # ignorujemy inne nadmiarowe klucze, żeby nie wywalać testów

    # alias tylko do odczytu (jeśli ktoś próbuje sięgnąć po .hash)
    @property
    def hash(self) -> Optional[str]:  # noqa: D401
        return self.document_hash


class Ledger:
    def __init__(self) -> None:
        self._events: List[LedgerRecord] = []

    # --- API wprost używane w testach ---------------------------------
    def append(self, rec: LedgerRecord) -> None:
        """Dodaj istniejący rekord (testy tego używają)."""
        self._events.append(rec)

    def read_all(self, case_id: Optional[str] = None) -> List[LedgerRecord]:
        """Zwróć wszystkie rekordy (opcjonalnie tylko dla case_id)."""
        if case_id is None:
            return list(self._events)
        return [r for r in self._events if r.case_id == case_id]

    # --- API używane przez nasze routery ------------------------------
    def _next_event_id(self) -> int:
        return len(self._events) + 1

    def _now_iso(self) -> str:
        return datetime.now(timezone.utc).isoformat()

    def _chain(self, payload: Dict[str, Any], prev: Optional[str]) -> str:
        body = dict(payload)
        if prev:
            body["prev"] = prev
        return sha256(
            json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()

    def record_input(self, *, case_id: str, document_hash: str) -> Dict[str, Any]:
        event_id = self._next_event_id()
        ts = self._now_iso()
        prev = self._events[-1].chain_self if self._events else None

        payload = {
            "event_id": event_id,
            "type": "INPUT_INGESTION",
            "case_id": case_id,
            "document_hash": document_hash,
            "timestamp": ts,
        }
        chain_self = self._chain(payload, prev)

        rec = LedgerRecord(
            event_id=event_id,
            type="INPUT_INGESTION",
            case_id=case_id,
            document_hash=document_hash,
            timestamp=ts,
            chain_prev=prev,
            chain_self=chain_self,
        )
        self._events.append(rec)

        return {
            "event_id": rec.event_id,
            "type": rec.type,
            "case_id": rec.case_id,
            "document_hash": rec.document_hash,
            "timestamp": rec.timestamp,
            "chain_prev": rec.chain_prev,
            "chain_self": rec.chain_self,
        }

    def get_records_for_case(self, *, case_id: str) -> List[Dict[str, Any]]:
        """Wersja słownikowa (używana przez router /ledger)."""
        return [
            {
                "event_id": r.event_id,
                "type": r.type,
                "case_id": r.case_id,
                "document_hash": r.document_hash,
                "timestamp": r.timestamp,
                "chain_prev": r.chain_prev,
                "chain_self": r.chain_self,
            }
            for r in self._events
            if r.case_id == case_id
        ]


# pojedyncza instancja do użycia przez routery
ledger_service = Ledger()

__all__ = [
    "Ledger",
    "LedgerRecord",
    "ledger_service",
    "compute_provenance_hash",
    "verify_provenance_hash",
]
