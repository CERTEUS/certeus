#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/mismatch_service/models.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/mismatch_service/models.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""Modele Pydantic v2 dla biletów niezgodności SMT."""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from datetime import UTC, datetime
from enum import Enum
from typing import Any

from pydantic import BaseModel, Field, field_validator

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

class TicketStatus(str, Enum):
    OPEN = "open"

    UNDER_REVIEW = "under_review"

    RESOLVED = "resolved"

    ESCALATED = "escalated"

    CLOSED = "closed"

class TicketPriority(str, Enum):
    LOW = "low"

    MEDIUM = "medium"

    HIGH = "high"

    CRITICAL = "critical"

class ResolutionType(str, Enum):
    HUMAN_OVERRIDE = "human_override"

    SOLVER_UPDATE = "solver_update"

    FORMULA_CORRECTION = "formula_correction"

    FALSE_POSITIVE = "false_positive"

    KNOWN_LIMITATION = "known_limitation"

class SolverResult(BaseModel):
    solver_name: str = Field(..., description="e.g. 'z3', 'cvc5'")

    status: str = Field(..., description="sat/unsat/unknown/timeout/error")

    execution_time_ms: float | None = Field(None)

    model: dict[str, Any] | None = Field(None)

    error_message: str | None = Field(None)

    version: str | None = Field(None)

    @field_validator("status")
    @classmethod
    def _status_ok(cls, v: str) -> str:
        valid = {"sat", "unsat", "unknown", "timeout", "error"}

        vv = (v or "").lower()

        if vv not in valid:
            raise ValueError(f"Invalid status: {v}. Must be one of {valid}")

        return vv

class MismatchTicket(BaseModel):
    ticket_id: str

    case_id: str

    formula_str: str

    formula_ast: dict[str, Any] | None = None

    formula_hash: str | None = None

    results: list[SolverResult]

    expected_result: str | None = None

    status: TicketStatus = TicketStatus.OPEN

    priority: TicketPriority = TicketPriority.MEDIUM

    created_at: datetime = Field(default_factory=lambda: datetime.now(UTC))

    updated_at: datetime | None = None

    resolved_at: datetime | None = None

    resolution_type: ResolutionType | None = None

    resolution_notes: str | None = None

    resolved_by: str | None = None

    chosen_result: str | None = None

    tags: list[str] = Field(default_factory=list)

    attachments: list[str] = Field(default_factory=list)

    model_config = {
        "use_enum_values": True,
        "ser_json_timedelta": "float",
    }

    @field_validator("priority", mode="before")
    @classmethod
    def _auto_priority(cls, v, info):
        if v:
            return v

        values = info.data

        results = values.get("results", [])

        statuses = [
            getattr(r, "status", None) if isinstance(r, SolverResult) else (r or {}).get("status") for r in results
        ]

        statuses = [s for s in statuses if s]

        if "sat" in statuses and "unsat" in statuses:
            return TicketPriority.CRITICAL

        if "error" in statuses:
            return TicketPriority.HIGH

        return TicketPriority.MEDIUM

    def get_mismatch_summary(self) -> str:
        if not self.results:
            return "No results"

        buckets: dict[str, list[str]] = {}

        for r in self.results:
            buckets.setdefault(r.status, []).append(r.solver_name)

        parts = [f"{k}({', '.join(v)})" for k, v in buckets.items()]

        return " vs ".join(parts)

class TicketResolution(BaseModel):
    ticket_id: str

    resolution_type: ResolutionType

    chosen_result: str

    notes: str

    resolved_by: str

    confidence: float = Field(..., ge=0.0, le=1.0)

    solver_update_info: dict[str, Any] | None = None

    formula_correction: str | None = None

class TicketStatistics(BaseModel):
    total_tickets: int = 0

    open_tickets: int = 0

    under_review_tickets: int = 0

    resolved_tickets: int = 0

    escalated_tickets: int = 0

    avg_resolution_time_hours: float | None = None

    most_common_mismatch: str | None = None

    by_priority: dict[str, int] = Field(default_factory=dict)

    by_resolution_type: dict[str, int] = Field(default_factory=dict)

    by_solver: dict[str, int] = Field(default_factory=dict)

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
