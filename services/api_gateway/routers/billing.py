#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/billing.py             |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/billing.py             |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla obszaru Billing / Cost‑Tokens.
EN: FastAPI router for Billing / Cost‑Tokens.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any
import uuid

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===

_DEFAULT_STATE_FILE = Path(__file__).resolve().parents[3] / "data" / "fin_tokens.json"


def _state_file() -> Path:
    override = os.getenv("CERTEUS_TEST_STATE_PATH")
    if override:
        return Path(override)
    return _DEFAULT_STATE_FILE


def _load_state() -> dict[str, Any]:
    sf = _state_file()
    if not sf.exists():
        return {"requests": {}}
    try:
        return json.loads(sf.read_text(encoding="utf-8"))
    except Exception:
        return {"requests": {}}


def _save_state(state: dict[str, Any]) -> None:
    sf = _state_file()
    sf.parent.mkdir(parents=True, exist_ok=True)
    sf.write_text(json.dumps(state, indent=2, ensure_ascii=False), encoding="utf-8")


# === MODELE / MODELS ===


class TokenRequestIn(BaseModel):
    user_id: str = Field(min_length=1)
    amount: int = Field(gt=0)
    purpose: str | None = None


class TokenRequestOut(BaseModel):
    request_id: str
    status: str
    user_id: str
    amount: int
    purpose: str | None = None


class TokenAllocateIn(BaseModel):
    request_id: str
    allocated_by: str | None = None


class TokenStatusOut(BaseModel):
    request_id: str
    status: str
    allocated_by: str | None = None


# === LOGIKA / LOGIC ===

router_tokens = APIRouter(prefix="/v1/fin/tokens", tags=["billing"])


@router_tokens.post("/request", response_model=TokenRequestOut)
async def request_tokens(req: TokenRequestIn, request: Request) -> TokenRequestOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load_state()
    rid = uuid.uuid4().hex
    entry = {
        "request_id": rid,
        "status": "PENDING",
        "user_id": req.user_id,
        "amount": int(req.amount),
        "purpose": req.purpose,
        "allocated_by": None,
    }
    state.setdefault("requests", {})[rid] = entry
    _save_state(state)
    return TokenRequestOut(**entry)


@router_tokens.post("/allocate", response_model=TokenStatusOut)
async def allocate_tokens(req: TokenAllocateIn, request: Request) -> TokenStatusOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load_state()
    entry = state.get("requests", {}).get(req.request_id)
    if not entry:
        raise HTTPException(status_code=404, detail="unknown request_id")
    if entry.get("status") == "ALLOCATED":
        return TokenStatusOut(request_id=req.request_id, status="ALLOCATED", allocated_by=entry.get("allocated_by"))
    entry["status"] = "ALLOCATED"
    if req.allocated_by:
        entry["allocated_by"] = req.allocated_by
    state["requests"][req.request_id] = entry
    _save_state(state)
    return TokenStatusOut(request_id=req.request_id, status="ALLOCATED", allocated_by=entry.get("allocated_by"))


@router_tokens.get("/{request_id}", response_model=TokenStatusOut)
async def get_request_status(request_id: str, request: Request) -> TokenStatusOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load_state()
    entry = state.get("requests", {}).get(request_id)
    if not entry:
        raise HTTPException(status_code=404, detail="unknown request_id")
    return TokenStatusOut(
        request_id=request_id, status=str(entry.get("status")), allocated_by=entry.get("allocated_by")
    )


class QuotaRequest(BaseModel):
    tenant: str | None = None
    units: int = Field(ge=0, default=0)


class AllocateRequest(BaseModel):
    cost_units: int = Field(ge=0)


class RefundRequest(BaseModel):
    units: int = Field(ge=0)


# Billing endpoints (per-tenant budgets)
router = APIRouter(prefix="/v1/billing", tags=["billing"])


@router.get("/quota")
async def quota(request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import get_tenant_balance, get_tenant_id

    tenant = get_tenant_id(request)
    return {"tenant": tenant, "balance": get_tenant_balance(tenant)}


@router.post("/quota")
async def set_quota_api(req: QuotaRequest, request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import get_tenant_balance, get_tenant_id, set_tenant_quota

    tenant = (req.tenant or get_tenant_id(request)).strip() or get_tenant_id(request)
    set_tenant_quota(tenant, max(0, int(req.units)))
    return {"ok": True, "tenant": tenant, "balance": get_tenant_balance(tenant)}


@router.post("/allocate")
async def allocate(req: AllocateRequest, request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import allocate_tenant_cost, get_tenant_balance, get_tenant_id

    tenant = get_tenant_id(request)
    if req.cost_units == 0:
        return {"status": "ALLOCATED", "tenant": tenant, "balance": get_tenant_balance(tenant)}
    ok = allocate_tenant_cost(tenant, int(req.cost_units))
    if not ok:
        return {"status": "PENDING", "tenant": tenant, "balance": get_tenant_balance(tenant)}
    return {"status": "ALLOCATED", "tenant": tenant, "balance": get_tenant_balance(tenant)}


@router.post("/refund")
async def refund(req: RefundRequest, request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import get_tenant_balance, get_tenant_id, refund_tenant_units

    tenant = get_tenant_id(request)
    if req.units > 0:
        refund_tenant_units(tenant, int(req.units))
    return {"ok": True, "tenant": tenant, "balance": get_tenant_balance(tenant)}
