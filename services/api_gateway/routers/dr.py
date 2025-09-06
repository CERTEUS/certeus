#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/dr.py                  |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/dr.py                  |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla obszaru Disaster Recovery: replay/revoke.

EN: FastAPI router for DR: replay/revoke.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class ReplayRequest(BaseModel):
    case: str

    timestamp: str


class ReplayResponse(BaseModel):
    ok: bool

    state_uri: str


class RecallRequest(BaseModel):
    upn: str


class RecallResponse(BaseModel):
    ok: bool

    link: str


class LockRequest(BaseModel):
    case: str = Field(..., min_length=1)
    reason: str | None = None


class LockResponse(BaseModel):
    ok: bool
    lock_ref: str


class RevokeRequest(BaseModel):
    lock_ref: str = Field(..., min_length=3)


class RevokeResponse(BaseModel):
    ok: bool
    revoked: bool


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/dr.py                            |

# | ROLE: DR-Replay / DR-Recall (stubs)                                 |

# +=====================================================================+

router = APIRouter(prefix="/v1/dr", tags=["DR"])


@router.post("/replay", response_model=ReplayResponse)
async def replay(req: ReplayRequest, request: Request) -> ReplayResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    return ReplayResponse(
        ok=True, state_uri=f"boundary://snapshot/{req.case}/{req.timestamp}"
    )


@router.post("/recall", response_model=RecallResponse)
async def recall(req: RecallRequest, request: Request) -> RecallResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    return RecallResponse(ok=True, link=f"ledger://revocations/{req.upn}")


@router.post("/lock", response_model=LockResponse)
async def lock(req: LockRequest, request: Request, response: Response) -> LockResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    lock_ref = f"lock://{req.case}/" + (req.reason or "hold")
    try:
        response.headers["X-CERTEUS-PCO-dr.lock"] = lock_ref
    except Exception:
        pass
    return LockResponse(ok=True, lock_ref=lock_ref)


@router.post("/revoke", response_model=RevokeResponse)
async def revoke(
    req: RevokeRequest, request: Request, response: Response
) -> RevokeResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    try:
        response.headers["X-CERTEUS-PCO-dr.revoke"] = req.lock_ref
    except Exception:
        pass
    return RevokeResponse(ok=True, revoked=True)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
