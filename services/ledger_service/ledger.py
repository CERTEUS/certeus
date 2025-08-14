# +-------------------------------------------------------------+
# |                   CERTEUS - Ledger Service                  |
# +-------------------------------------------------------------+
# | PLIK / FILE: services/ledger_service/ledger.py              |
# | ROLA / ROLE: Niezmienna księga pochodzenia (hash chaining). |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
import logging
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from hashlib import sha256
from threading import Lock
from typing import Any, Final, Literal

log = logging.getLogger("certeus.ledger")
if not log.handlers:  # idempotent
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(name)s: %(message)s")

EventType = Literal["INPUT_INGESTION"]


@dataclass(frozen=True, slots=True)
class _LedgerRecord:
    """
    PL: Kanoniczna reprezentacja zapisu księgi.
    EN: Canonical representation of a ledger record.
    """
    event_id: int
    type: EventType
    case_id: str
    document_hash: str
    timestamp: str  # RFC3339
    chain_prev: str | None
    chain_self: str


def _now_iso() -> str:
    """PL: Czas UTC ISO-8601. EN: UTC ISO-8601 time."""
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def _canonical(obj: dict[str, Any]) -> str:
    """PL/EN: Deterministyczna serializacja JSON (sort keys)."""
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


class LedgerService:
    """
    PL: Serwis księgi z łańcuchowaniem hashy i blokadą wątkową (append-only).
    EN: Append-only ledger with hash chaining and thread-safety.
    """

    _GENESIS: Final[str] = "GENESIS"

    def __init__(self) -> None:
        self._lock: Final[Lock] = Lock()
        self._records: list[_LedgerRecord] = []
        self._last_hash: str | None = None
        log.info("LedgerService initialized (in-memory, append-only).")

    # --- API ZDARZEŃ / EVENT API ---
    def record_input(self, case_id: str, document_hash: str) -> dict[str, Any]:
        """
        PL: Rejestruje przyjęcie dokumentu do systemu.
        EN: Records ingestion of a document into the system.
        """
        # Pylance miał rację: isinstance(str, str) zbędne — mamy adnotacje typów.
        case_id = case_id.strip()
        document_hash = document_hash.strip()

        if not case_id:
            raise ValueError("case_id must be a non-empty string.")
        if not document_hash:
            raise ValueError("document_hash must be a non-empty string.")

        payload = {
            "type": "INPUT_INGESTION",
            "case_id": case_id,
            "document_hash": document_hash,
        }
        return self._append(payload)

    # --- ODCZYT / READ ---
    def get_records_for_case(self, case_id: str) -> list[dict[str, Any]]:
        """PL: Zwraca kopie zapisów dla danej sprawy. EN: Returns copies for given case."""
        with self._lock:
            out: list[dict[str, Any]] = []
            for rec in self._records:
                if rec.case_id == case_id:
                    out.append(dict(asdict(rec)))
            return out

    # --- CORE APPEND ---
    def _append(self, core: dict[str, Any]) -> dict[str, Any]:
        """PL: Dodaje zdarzenie; nadaje ID/czas; łańcuchuje hash. EN: Append event; chain hash."""
        with self._lock:
            event_id = len(self._records) + 1
            timestamp = _now_iso()
            prev = self._last_hash or self._GENESIS

            canon = _canonical({"event_id": event_id, "timestamp": timestamp, **core})
            digest = sha256((prev + "|" + canon).encode("utf-8")).hexdigest()

            record = _LedgerRecord(
                event_id=event_id,
                type=core["type"],
                case_id=core["case_id"],
                document_hash=core["document_hash"],
                timestamp=timestamp,
                chain_prev=None if self._last_hash is None else self._last_hash,
                chain_self=digest,
            )
            self._records.append(record)
            self._last_hash = digest
            log.info("LEDGER append: #%s %s %s", event_id, record.type, record.case_id)
            return dict(asdict(record))


# === INSTANCJA SINGLETON / SINGLETON INSTANCE ===
ledger_service = LedgerService()
