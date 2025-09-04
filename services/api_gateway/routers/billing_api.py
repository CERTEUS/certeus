#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/billing_api.py          |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/billing_api.py          |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Router FastAPI — Billing (quota/allocate/refund) oparty o limits hook.

EN: FastAPI router — Billing (quota/allocate/refund) backed by limits hook.
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

# === MODELE / MODELS ===


class AllocateIn(BaseModel):
    cost_units: int = Field(gt=0)


class RefundIn(BaseModel):
    units: int = Field(gt=0)


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/billing", tags=["billing"])


@router.get("/quota")
async def get_quota(request: Request) -> dict[str, int | str]:
    tenant = get_tenant_id(request)
    bal = get_tenant_balance(tenant)
    return {"tenant": tenant, "balance": int(bal)}


@router.post("/allocate")
async def allocate(request: Request, body: AllocateIn) -> dict[str, str | int]:
    tenant = get_tenant_id(request)
    ok = allocate_tenant_cost(tenant, int(body.cost_units))
    status = "ALLOCATED" if ok else "PENDING"
    return {"tenant": tenant, "status": status}


@router.post("/refund")
async def refund(request: Request, body: RefundIn) -> dict[str, int | str]:
    tenant = get_tenant_id(request)
    bal = refund_tenant_units(tenant, int(body.units))
    return {"tenant": tenant, "balance": int(bal)}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
