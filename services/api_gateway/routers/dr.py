#!/usr/bin/env python3
"""
PL: Router FastAPI dla obszaru Disaster Recovery: replay/revoke.

EN: FastAPI router for DR: replay/revoke.
"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===


#!/usr/bin/env python3


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/dr.py                            |

# | ROLE: DR-Replay / DR-Recall (stubs)                                 |

# +=====================================================================+

from __future__ import annotations

from fastapi import APIRouter, Request
from pydantic import BaseModel

router = APIRouter(prefix="/v1/dr", tags=["DR"])


class ReplayRequest(BaseModel):
    case: str

    timestamp: str


class ReplayResponse(BaseModel):
    ok: bool

    state_uri: str


@router.post("/replay", response_model=ReplayResponse)
async def replay(req: ReplayRequest, request: Request) -> ReplayResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    return ReplayResponse(ok=True, state_uri=f"boundary://snapshot/{req.case}/{req.timestamp}")


class RecallRequest(BaseModel):
    upn: str


class RecallResponse(BaseModel):
    ok: bool

    link: str


@router.post("/recall", response_model=RecallResponse)
async def recall(req: RecallRequest, request: Request) -> RecallResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    return RecallResponse(ok=True, link=f"ledger://revocations/{req.upn}")
