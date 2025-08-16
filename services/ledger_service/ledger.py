# +-------------------------------------------------------------+
# |                        CERTEUS                              |
# |        Core Engine for Reliable & Unified Systems           |
# +-------------------------------------------------------------+
# ── CERTEUS Project ─────────────────────────────────────────────────────────────
# File: services/ledger_service/ledger.py
# License: Apache-2.0
# Description (PL): Minimalny, testowalny rejestr pochodzenia danych (hash→parent→timestamp).
# Description (EN): Minimal, testable provenance ledger (hash→parent→timestamp).
# Style Guide: ASCII header, PL/EN docs, labeled code blocks, type hints.
# ────────────────────────────────────────────────────────────────

"""
PL:
  Ten moduł dostarcza Ledger – prosty, deterministyczny rejestr pochodzenia:
  - Każdy wpis identyfikowany przez sha256:... bajtów „ładunku”.
  - Relacja parent_id buduje łańcuch custody.
  - Czas tworzenia injektowalny (łatwiejsze testy).

EN:
  This module provides a simple, deterministic provenance Ledger:
  - Each record identified by sha256:... of the payload bytes.
  - parent_id builds the custody chain.
  - Creation time is injectable (easier tests).
"""

# [BLOCK: IMPORTS]
from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import Callable, Dict, Optional, List
import hashlib
import json
import time


# [BLOCK: DATA MODEL]
@dataclass(frozen=True)
class LedgerRecord:
    """PL/EN: Single ledger entry."""

    id: str  # sha256:<64hex>
    parent_id: Optional[str]
    stage: str  # e.g., "input", "ocr", "map", "export"
    payload_sha256: str  # redundant, equals id
    created_at: float  # epoch seconds


# [BLOCK: LEDGER]
class Ledger:
    """
    PL: Rejestr pochodzenia z injektowalnym zegarem i prostymi gwarancjami spójności.
    EN: Provenance ledger with injectable clock and simple consistency checks.
    """

    def __init__(self, *, now: Callable[[], float] | None = None) -> None:
        self._now: Callable[[], float] = now if now is not None else time.time
        self._records: Dict[str, LedgerRecord] = {}

    # [BLOCK: HASH]
    @staticmethod
    def _sha256_id(payload: bytes) -> str:
        """PL/EN: Returns 'sha256:<hexdigest>' for given bytes."""
        return "sha256:" + hashlib.sha256(payload).hexdigest()

    # [BLOCK: RECORD INPUT]
    def record_input(self, payload: bytes, *, stage: str = "input") -> LedgerRecord:
        """
        PL: Rejestruje oryginalny „ładunek” źródłowy. Zwraca istniejący wpis, jeśli hash był już zapisany.
        EN: Records the original source payload. Returns existing record if hash already present.
        """
        rid = self._sha256_id(payload)
        if rid in self._records:
            return self._records[rid]
        rec = LedgerRecord(
            id=rid,
            parent_id=None,
            stage=stage,
            payload_sha256=rid,
            created_at=self._now(),
        )
        self._records[rid] = rec
        return rec

    # [BLOCK: RECORD TRANSFORM]
    def record_transform(
        self, parent: LedgerRecord | str, payload: bytes, *, stage: str
    ) -> LedgerRecord:
        """
        PL: Rejestruje przekształcenie – tworzy nowy hash i wskazuje parent_id.
        EN: Records a transformation – creates a new hash and points to parent_id.
        """
        parent_id = parent.id if isinstance(parent, LedgerRecord) else parent
        if parent_id not in self._records:
            raise KeyError(f"Unknown parent_id: {parent_id}")
        cid = self._sha256_id(payload)
        if cid in self._records:
            # Jeśli już istnieje, upewnij się, że łańcuch jest spójny.
            return self._records[cid]
        rec = LedgerRecord(
            id=cid,
            parent_id=parent_id,
            stage=stage,
            payload_sha256=cid,
            created_at=self._now(),
        )
        self._records[cid] = rec
        return rec

    # [BLOCK: RECORD EXPORT]
    def record_export(self, parent: LedgerRecord | str, payload: bytes) -> LedgerRecord:
        """PL/EN: Convenience wrapper for final export stage."""
        return self.record_transform(parent, payload, stage="export")

    # [BLOCK: ACCESSORS]
    def get(self, record_id: str) -> LedgerRecord:
        """PL/EN: Retrieves a record by id, raises KeyError if missing."""
        return self._records[record_id]

    def ancestry(self, record_id: str) -> List[str]:
        """PL/EN: Returns the ancestry chain [root..record_id]."""
        chain: List[str] = []
        cur = self._records[record_id]
        while cur is not None:
            chain.append(cur.id)
            cur = self._records[cur.parent_id] if cur.parent_id else None
        return list(reversed(chain))

    def validate_chain(self) -> bool:
        """
        PL: Sprawdza referencje parent_id i format id (sha256:...).
        EN: Checks parent references and id format (sha256:...).
        """
        for rec in self._records.values():
            if not rec.id.startswith("sha256:") or not rec.payload_sha256.startswith(
                "sha256:"
            ):
                return False
            if rec.parent_id is not None and rec.parent_id not in self._records:
                return False
        return True

    # [BLOCK: EXPORT]
    def to_json(self) -> str:
        """PL/EN: JSON dump for audit/debug."""
        return json.dumps(
            [asdict(r) for r in self._records.values()], ensure_ascii=False, indent=2
        )

    # [BLOCK: LEN]
    def __len__(self) -> int:  # pragma: no cover
        return len(self._records)
