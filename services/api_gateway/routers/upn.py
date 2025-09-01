#!/usr/bin/env python3
"""
PL: Router FastAPI dla obszaru rejestr UPN.

EN: FastAPI router for UPN registry.
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

# | FILE: services/api_gateway/routers/upn.py                           |

# | ROLE: UPN Registry & Revocation (stub)                              |

# +=====================================================================+

from __future__ import annotations

import time
from typing import Any

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, Field

router = APIRouter(prefix="/v1/upn", tags=["UPN"])


class RegisterRequest(BaseModel):
    subject: dict[str, Any]

    claims: list[dict[str, Any]] | None = None


class RegisterResponse(BaseModel):
    upn: str

    ts: int

    ledger_ref: str | None = None


_REGISTRY: dict[str, dict[str, Any]] = {}

_COUNTER = 1


@router.post("/register", response_model=RegisterResponse)
async def register(req: RegisterRequest, request: Request) -> RegisterResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    global _COUNTER

    ts = int(time.time())

    upn = f"UPN-{ts}-{_COUNTER:06d}"

    _COUNTER += 1

    _REGISTRY[upn] = {"subject": req.subject, "claims": req.claims or [], "revoked": False, "ts": ts}

    return RegisterResponse(upn=upn, ts=ts, ledger_ref=None)


class RevokeRequest(BaseModel):
    upn: str = Field(description="Identifier returned by /register")

    reason: str | None = None


class RevokeResponse(BaseModel):
    upn: str

    revoked: bool

    merkle_proof: dict[str, Any]


@router.post("/revoke", response_model=RevokeResponse)
async def revoke(req: RevokeRequest, request: Request) -> RevokeResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    rec = _REGISTRY.get(req.upn)

    if not rec:
        raise HTTPException(status_code=404, detail="UPN not found")

    rec["revoked"] = True

    # Stub Merkle-proof

    proof = {"path": [], "root": "0" * 64}

    return RevokeResponse(upn=req.upn, revoked=True, merkle_proof=proof)
