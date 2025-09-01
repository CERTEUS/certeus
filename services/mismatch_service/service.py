#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/mismatch_service/service.py                |

# | ROLE: Project module.                                       |

# | PLIK: services/mismatch_service/service.py                |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""Serwis do zarządzania biletami niezgodności między solverami SMT."""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from collections import defaultdict
from collections.abc import Callable
from datetime import UTC, datetime
import json
import logging
from pathlib import Path
from typing import Any
import uuid

from .models import (
    MismatchTicket,
    SolverResult,
    TicketPriority,
    TicketResolution,
    TicketStatistics,
    TicketStatus,
)

# === KONFIGURACJA / CONFIGURATION ===
STORAGE_MODE = "memory"  # "file" w razie potrzeby


# === MODELE / MODELS ===
class MismatchService:
    def __init__(self, storage_mode: str = STORAGE_MODE) -> None:
        self.storage_mode = storage_mode

        self._tickets: dict[str, MismatchTicket] = {}

        self._resolution_callbacks: list[Callable[[MismatchTicket, TicketResolution], None]] = []

        if storage_mode == "file":
            STORAGE_PATH.mkdir(parents=True, exist_ok=True)

            self._load_from_disk()

        logger.info(
            "MismatchService init (mode=%s, tickets=%s)",
            storage_mode,
            len(self._tickets),
        )

    # -- Creation --------------------------------------------------------

    def create_ticket(
        self,
        case_id: str,
        formula_str: str,
        results: dict[str, Any],
        formula_ast: dict[str, Any] | None = None,
        priority: TicketPriority | None = None,
    ) -> MismatchTicket:
        ticket_id = f"MM-{uuid.uuid4().hex[:8].upper()}"

        solver_results: list[SolverResult] = []

        for solver_name, data in results.items():
            if isinstance(data, dict):
                solver_results.append(
                    SolverResult(
                        solver_name=solver_name,
                        status=data.get("status", "unknown"),
                        execution_time_ms=data.get("time_ms"),
                        model=data.get("model"),
                        error_message=data.get("error"),
                        version=data.get("version"),
                    )
                )

        # Upewnij się, że priority ma typ TicketPriority (nie None)

        prio: TicketPriority = priority if priority is not None else TicketPriority.MEDIUM

        ticket = MismatchTicket(
            ticket_id=ticket_id,
            case_id=case_id,
            formula_str=formula_str,
            formula_ast=formula_ast,
            results=solver_results,
            priority=prio,
        )

        self._tickets[ticket_id] = ticket

        self._persist_if_needed()

        self._log_critical_alert(ticket)

        return ticket

    def _log_critical_alert(self, ticket: MismatchTicket) -> None:
        box = [
            "",
            "=" * 80,
            "🚨 CRITICAL ALERT: SOLVER MISMATCH DETECTED! 🚨",
            "=" * 80,
            f"Ticket ID: {ticket.ticket_id}",
            f"Case ID: {ticket.case_id}",
            f"Priority: {ticket.priority}",
            f"Mismatch: {ticket.get_mismatch_summary()}",
            "=" * 80,
            "⚠️  HUMAN INTERVENTION REQUIRED  ⚠️",
            "=" * 80,
            "",
        ]

        for line in box:
            logger.critical(line)

    # -- Retrieval -------------------------------------------------------

    def get_ticket(self, ticket_id: str) -> MismatchTicket | None:
        return self._tickets.get(ticket_id)

    def get_all_tickets(self) -> list[MismatchTicket]:
        return list(self._tickets.values())

    def get_open_tickets(self) -> list[MismatchTicket]:
        return [t for t in self._tickets.values() if t.status == TicketStatus.OPEN]

    def get_tickets_by_status(self, status: TicketStatus) -> list[MismatchTicket]:
        return [t for t in self._tickets.values() if t.status == status]

    def get_tickets_by_case(self, case_id: str) -> list[MismatchTicket]:
        return [t for t in self._tickets.values() if t.case_id == case_id]

    # -- Resolution / Escalation ----------------------------------------

    def resolve_ticket(self, ticket_id: str, resolution: TicketResolution) -> MismatchTicket:
        ticket = self._tickets.get(ticket_id)

        if not ticket:
            raise KeyError(f"Ticket not found: {ticket_id}")

        if ticket.status == TicketStatus.RESOLVED:
            raise ValueError(f"Ticket already resolved: {ticket_id}")

        ticket.status = TicketStatus.RESOLVED

        ticket.resolved_at = datetime.now(UTC)

        ticket.resolution_type = resolution.resolution_type

        ticket.resolution_notes = resolution.notes

        ticket.resolved_by = resolution.resolved_by

        ticket.chosen_result = resolution.chosen_result

        ticket.updated_at = datetime.now(UTC)

        self._persist_if_needed()

        for cb in self._resolution_callbacks:
            try:
                cb(ticket, resolution)

            except Exception as e:
                logger.error("Resolution callback failed: %s", e)

        logger.info(
            "Ticket %s resolved (type=%s, by=%s)",
            ticket_id,
            resolution.resolution_type,
            resolution.resolved_by,
        )

        return ticket

    def escalate_ticket(self, ticket_id: str, reason: str, escalated_by: str) -> MismatchTicket:
        ticket = self._tickets.get(ticket_id)

        if not ticket:
            raise KeyError(f"Ticket not found: {ticket_id}")

        ticket.status = TicketStatus.ESCALATED

        ticket.priority = TicketPriority.CRITICAL

        ticket.updated_at = datetime.now(UTC)

        note = f"[{datetime.now(UTC).isoformat()}] Escalated by {escalated_by}: {reason}"

        ticket.resolution_notes = ((ticket.resolution_notes + "\n") if ticket.resolution_notes else "") + note

        self._persist_if_needed()

        logger.warning("Ticket %s escalated by %s: %s", ticket_id, escalated_by, reason)

        return ticket

    # -- Stats -----------------------------------------------------------

    def get_statistics(self) -> TicketStatistics:
        stats = TicketStatistics()

        if not self._tickets:
            return stats

        status_counts = defaultdict(int)

        priority_counts = defaultdict(int)

        resolution_counts = defaultdict(int)

        solver_counts = defaultdict(int)

        resolution_times: list[float] = []

        for t in self._tickets.values():
            status_counts[t.status] += 1

            priority_counts[t.priority] += 1

            if t.resolution_type:
                resolution_counts[t.resolution_type] += 1

            for r in t.results:
                solver_counts[r.solver_name] += 1

            if t.resolved_at and t.created_at:
                resolution_times.append((t.resolved_at - t.created_at).total_seconds() / 3600.0)

        stats.total_tickets = len(self._tickets)

        stats.open_tickets = status_counts.get(TicketStatus.OPEN, 0)

        stats.under_review_tickets = status_counts.get(TicketStatus.UNDER_REVIEW, 0)

        stats.resolved_tickets = status_counts.get(TicketStatus.RESOLVED, 0)

        stats.escalated_tickets = status_counts.get(TicketStatus.ESCALATED, 0)

        stats.by_priority = dict(priority_counts)

        stats.by_resolution_type = dict(resolution_counts)

        stats.by_solver = dict(solver_counts)

        if resolution_times:
            stats.avg_resolution_time_hours = sum(resolution_times) / len(resolution_times)

        return stats

    # -- Persistence -----------------------------------------------------

    def _persist_if_needed(self) -> None:
        if self.storage_mode == "file":
            self._save_to_disk()

    def _save_to_disk(self) -> None:
        for ticket_id, ticket in self._tickets.items():
            p = STORAGE_PATH / f"{ticket_id}.json"

            with open(p, "w", encoding="utf-8") as f:
                json.dump(ticket.model_dump(), f, indent=2, default=str)

    def _load_from_disk(self) -> None:
        if not STORAGE_PATH.exists():
            return

        for p in STORAGE_PATH.glob("MM-*.json"):
            try:
                with open(p, encoding="utf-8") as f:
                    data = json.load(f)

                t = MismatchTicket(**data)

                self._tickets[t.ticket_id] = t

            except Exception as e:
                logger.error("Failed to load ticket %s: %s", p, e)

    # -- Callbacks -------------------------------------------------------

    def register_resolution_callback(self, callback: Callable[[MismatchTicket, TicketResolution], None]) -> None:
        self._resolution_callbacks.append(callback)

        logger.debug(
            "Registered resolution callback: %s",
            getattr(callback, "__name__", str(callback)),
        )


# === LOGIKA / LOGIC ===


STORAGE_PATH = Path("data/mismatch_tickets")


#!/usr/bin/env python3


logger = logging.getLogger(__name__)


# Singleton

mismatch_service = MismatchService()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
