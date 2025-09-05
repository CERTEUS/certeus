#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/billing_quota.py        |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/billing_quota.py        |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla Billing (quota/allocate/refund) — in-memory bank
    jednostek z `services.api_gateway.limits`.

EN: FastAPI router for Billing (quota/allocate/refund) — in-memory token
    bank from `services.api_gateway.limits`.

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

@router.get("/quota", operation_id="billing_quota_get")
async def get_quota(request: Request) -> dict[str, int]:
    tenant = get_tenant_id(request)
    return {"balance": int(get_tenant_balance(tenant))}

@router.post("/allocate", operation_id="billing_quota_allocate")
async def allocate(req: AllocateRequest, request: Request) -> dict[str, str | int]:
    tenant = get_tenant_id(request)
    ok = allocate_tenant_cost(tenant, int(req.cost_units))
    status = "ALLOCATED" if ok else "PENDING"
    return {"status": status, "balance": int(get_tenant_balance(tenant))}

@router.post("/refund", operation_id="billing_quota_refund")
async def refund(req: RefundRequest, request: Request) -> dict[str, int]:
    tenant = get_tenant_id(request)
    bal = refund_tenant_units(tenant, int(req.units))
    return {"balance": int(bal)}

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
