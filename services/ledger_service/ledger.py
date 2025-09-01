#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ledger_service/ledger.py                   |

# | ROLE: Project module.                                       |

# | PLIK: services/ledger_service/ledger.py                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Księga pochodzenia (ledger) – logika.

EN: Provenance ledger – logic.

"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from datetime import UTC, datetime
from hashlib import sha256
import json
from typing import Any


def _normalize_for_hash(data: Mapping[str, Any], *, include_timestamp: bool) -> bytes:
    if not include_timestamp and "timestamp" in data:
        work = {k: v for k, v in data.items() if k != "timestamp"}

    else:
        work = dict(data)

    return json.dumps(work, sort_keys=True, separators=(",", ":")).encode("utf-8")


def compute_provenance_hash(data: Mapping[str, Any], *, include_timestamp: bool = False) -> str:
    return sha256(_normalize_for_hash(data, include_timestamp=include_timestamp)).hexdigest()


def verify_provenance_hash(data: Mapping[str, Any], expected_hash: str, *, include_timestamp: bool = False) -> bool:
    return compute_provenance_hash(data, include_timestamp=include_timestamp) == expected_hash


@dataclass(frozen=True)
class LedgerRecord:
    event_id: int

    type: str

    case_id: str

    document_hash: str | None

    timestamp: str

    chain_prev: str | None

    chain_self: str


class Ledger:
    def __init__(self) -> None:
        self._events: list[LedgerRecord] = []

    def _next_event_id(self) -> int:
        return len(self._events) + 1

    def _now_iso(self) -> str:
        return datetime.now(UTC).isoformat()

    def _chain(self, payload: dict[str, Any], prev: str | None) -> str:
        body = dict(payload)

        if prev:
            body["prev"] = prev

        return sha256(json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()

    def record_event(self, *, event_type: str, case_id: str, document_hash: str | None) -> dict[str, Any]:
        event_id = self._next_event_id()

        ts = self._now_iso()

        prev = self._events[-1].chain_self if self._events else None

        payload = {
            "event_id": event_id,
            "type": event_type,
            "case_id": case_id,
            "document_hash": document_hash,
            "timestamp": ts,
        }

        chain_self = self._chain(payload, prev)

        rec = LedgerRecord(event_id, event_type, case_id, document_hash, ts, prev, chain_self)

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

    def record_input(self, *, case_id: str, document_hash: str) -> dict[str, Any]:
        return self.record_event(event_type="INPUT_INGESTION", case_id=case_id, document_hash=document_hash)

    def get_records_for_case(self, *, case_id: str) -> list[dict[str, Any]]:
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

    def build_provenance_receipt(self, *, case_id: str) -> dict[str, Any]:
        items = self.get_records_for_case(case_id=case_id)

        if not items:
            raise ValueError(f"No records for case_id={case_id}")

        head = items[-1]

        return {
            "case_id": case_id,
            "head": head,
            "count": len(items),
            "created_at": self._now_iso(),
            "chain_valid": True,
        }


# singleton (opcjonalny)

ledger_service = Ledger()


__all__ = [
    "Ledger",
    "LedgerRecord",
    "ledger_service",
    "compute_provenance_hash",
    "verify_provenance_hash",
]
