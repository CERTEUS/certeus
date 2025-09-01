#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/mismatch.py            |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/mismatch.py            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Router FastAPI dla usług CERTEUS.

EN: FastAPI router for CERTEUS services.

"""

#!/usr/bin/env python3

from __future__ import annotations

from typing import Any

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field

from services.mismatch_service.models import TicketPriority
from services.mismatch_service.service import mismatch_service

router = APIRouter(prefix="/mismatch", tags=["mismatch"])


class EngineResult(BaseModel):
    status: str

    time_ms: float | None = None

    model: dict[str, Any] | None = None

    error: str | None = None

    version: str | None = None


class MismatchCreateRequest(BaseModel):
    case_id: str

    formula_str: str

    results: dict[str, EngineResult]

    formula_ast: dict[str, Any] | None = None

    priority: TicketPriority | None = Field(default=None)


@router.post("/tickets")
def create_ticket(req: MismatchCreateRequest) -> dict[str, Any]:
    t = mismatch_service.create_ticket(
        case_id=req.case_id,
        formula_str=req.formula_str,
        results={k: v.model_dump() for k, v in req.results.items()},
        formula_ast=req.formula_ast,
        priority=req.priority,
    )

    return t.model_dump()


@router.get("/tickets/{ticket_id}")
def get_ticket(ticket_id: str) -> dict[str, Any]:
    t = mismatch_service.get_ticket(ticket_id)

    if not t:
        raise HTTPException(status_code=404, detail="Ticket not found")

    return t.model_dump()
