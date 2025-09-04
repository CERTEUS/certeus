#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/billing.py              |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/billing.py              |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla Billing (quota/allocate/refund) — w oparciu o in-memory
    bank jednostek w `services.api_gateway.limits`.

EN: FastAPI router for Billing (quota/allocate/refund) — based on in-memory
    token bank in `services.api_gateway.limits`.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, Request
from pydantic import BaseModel, Field

from services.api_gateway.limits import (
    allocate_tenant_cost,
    get_tenant_balance,
    get_tenant_id,
    refund_tenant_units,
)

# === KONFIGURACJA / CONFIGURATION ===

router = APIRouter(prefix="/v1/billing", tags=["Billing"])


# === MODELE / MODELS ===


class AllocateRequest(BaseModel):
    cost_units: int = Field(..., ge=0)


class RefundRequest(BaseModel):
    units: int = Field(..., ge=0)


# === LOGIKA / LOGIC ===


@router.get("/quota")
async def get_quota(request: Request) -> dict[str, int]:
    tenant = get_tenant_id(request)
    return {"balance": int(get_tenant_balance(tenant))}


@router.post("/allocate")
async def allocate(req: AllocateRequest, request: Request) -> dict[str, str | int]:
    tenant = get_tenant_id(request)
    ok = allocate_tenant_cost(tenant, int(req.cost_units))
    status = "ALLOCATED" if ok else "PENDING"
    return {"status": status, "balance": int(get_tenant_balance(tenant))}


@router.post("/refund")
async def refund(req: RefundRequest, request: Request) -> dict[str, int]:
    tenant = get_tenant_id(request)
    bal = refund_tenant_units(tenant, int(req.units))
    return {"balance": int(bal)}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
