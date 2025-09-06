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


@router_tokens.post("/request", response_model=TokenRequestOut, operation_id="fin_request_tokens")
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
    try:
        from monitoring.metrics_slo import (
            certeus_billing_token_pending,
            certeus_billing_token_requests_total,
        )

        certeus_billing_token_requests_total.inc()
        certeus_billing_token_pending.inc()
    except Exception:
        pass
    return TokenRequestOut(**entry)


@router_tokens.post("/allocate", response_model=TokenStatusOut, operation_id="fin_allocate_tokens")
async def allocate_tokens(req: TokenAllocateIn, request: Request) -> TokenStatusOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load_state()
    entry = state.get("requests", {}).get(req.request_id)
    if not entry:
        raise HTTPException(status_code=404, detail="unknown request_id")
    if entry.get("status") == "ALLOCATED":
        return TokenStatusOut(
            request_id=req.request_id,
            status="ALLOCATED",
            allocated_by=entry.get("allocated_by"),
        )
    entry["status"] = "ALLOCATED"
    if req.allocated_by:
        entry["allocated_by"] = req.allocated_by
    state["requests"][req.request_id] = entry
    _save_state(state)
    try:
        from monitoring.metrics_slo import (
            certeus_billing_token_allocations_total,
            certeus_billing_token_pending,
        )

        certeus_billing_token_allocations_total.inc()
        # Decrement pending if >0
        try:
            cur = certeus_billing_token_pending._value.get()  # type: ignore[attr-defined]
            if cur > 0:
                certeus_billing_token_pending.dec()
        except Exception:
            pass
    except Exception:
        pass
    return TokenStatusOut(
        request_id=req.request_id,
        status="ALLOCATED",
        allocated_by=entry.get("allocated_by"),
    )


@router_tokens.get(
    "/{request_id}",
    response_model=TokenStatusOut,
    operation_id="fin_get_token_request_status",
)
async def get_request_status(request_id: str, request: Request) -> TokenStatusOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load_state()
    entry = state.get("requests", {}).get(request_id)
    if not entry:
        raise HTTPException(status_code=404, detail="unknown request_id")
    return TokenStatusOut(
        request_id=request_id,
        status=str(entry.get("status")),
        allocated_by=entry.get("allocated_by"),
    )


class QuotaRequest(BaseModel):
    tenant: str | None = None
    units: int = Field(ge=0, default=0)


class AllocateRequest(BaseModel):
    cost_units: int = Field(ge=0, alias="units")

    model_config = {
        "populate_by_name": True,
    }


class RefundRequest(BaseModel):
    units: int = Field(ge=0)


# Billing endpoints (per-tenant budgets)
router = APIRouter(prefix="/v1/billing", tags=["billing"])


@router.get("/quota", operation_id="billing_get_quota")
async def quota(request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import get_tenant_balance, get_tenant_id

    tenant = get_tenant_id(request)
    return {"tenant": tenant, "balance": get_tenant_balance(tenant)}


@router.post("/quota", operation_id="billing_set_quota")
async def set_quota_api(req: QuotaRequest, request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import (
        get_tenant_balance,
        get_tenant_id,
        set_tenant_quota,
    )

    tenant = (req.tenant or get_tenant_id(request)).strip() or get_tenant_id(request)
    set_tenant_quota(tenant, max(0, int(req.units)))
    return {"ok": True, "tenant": tenant, "balance": get_tenant_balance(tenant)}


@router.post("/allocate", operation_id="billing_allocate_units")
async def allocate(req: AllocateRequest, request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import (
        allocate_tenant_cost,
        get_tenant_balance,
        get_tenant_id,
    )

    tenant = get_tenant_id(request)
    if req.cost_units == 0:
        return {
            "status": "ALLOCATED",
            "tenant": tenant,
            "balance": get_tenant_balance(tenant),
        }
    ok = allocate_tenant_cost(tenant, int(req.cost_units))
    if not ok:
        return {
            "status": "PENDING",
            "tenant": tenant,
            "balance": get_tenant_balance(tenant),
        }
    return {
        "status": "ALLOCATED",
        "tenant": tenant,
        "balance": get_tenant_balance(tenant),
    }


@router.post("/refund", operation_id="billing_refund_units")
async def refund(req: RefundRequest, request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import (
        get_tenant_balance,
        get_tenant_id,
        refund_tenant_units,
    )

    tenant = get_tenant_id(request)
    if req.units > 0:
        refund_tenant_units(tenant, int(req.units))
    return {"ok": True, "tenant": tenant, "balance": get_tenant_balance(tenant)}


# --------------------- Policies / Admin / Estimate ---------------------

_POLICY_CACHE: dict[str, Any] | None = None


def _policy_file_path() -> Path:
    p = os.getenv("BILLING_POLICY_FILE")
    return Path(p) if p else (Path(__file__).resolve().parents[3] / "data" / "billing_policy.json")


def _load_policy() -> dict[str, Any]:
    global _POLICY_CACHE
    if _POLICY_CACHE is not None:
        return _POLICY_CACHE
    path = _policy_file_path()
    if path.exists():
        try:
            _POLICY_CACHE = json.loads(path.read_text(encoding="utf-8"))
            if isinstance(_POLICY_CACHE, dict):
                return _POLICY_CACHE
        except Exception:
            _POLICY_CACHE = None
    # default policy
    default = {
        "tiers": {
            "free": {"daily_quota": 1000},
            "pro": {"daily_quota": 100000},
            "enterprise": {"daily_quota": 1000000},
        },
        "tenants": {},
    }
    _POLICY_CACHE = default
    return default


def _save_policy(pol: dict[str, Any]) -> None:
    global _POLICY_CACHE
    _POLICY_CACHE = pol
    if (os.getenv("BILLING_POLICY_FILE_WRITE") or "").strip() in {"1", "true", "True"}:
        path = _policy_file_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(pol, ensure_ascii=False, indent=2), encoding="utf-8")


@router.get("/policies", summary="Get billing policies (tiers and tenants)")
async def get_policies() -> dict[str, Any]:
    return _load_policy()


@router.get("/tenant_tier", summary="Resolve tenant tier")
async def tenant_tier(request: Request) -> dict[str, str]:
    from services.api_gateway.limits import get_tenant_id

    pol = _load_policy()
    tenant = get_tenant_id(request)
    tier = pol.get("tenants", {}).get(tenant) or "free"
    return {"tenant": tenant, "tier": tier}


@router.post("/estimate", summary="Estimate cost units for action")
async def estimate(body: dict[str, Any], request: Request) -> dict[str, Any]:
    from services.api_gateway.limits import get_tenant_id

    tenant = get_tenant_id(request)
    action = str(body.get("action") or "").strip()
    table = {"qtm.measure": 2}
    units = int(table.get(action, 1))
    return {"tenant": tenant, "action": action, "estimated_units": units}


@router.get("/recommendation", summary="Recommend tier based on action and volume")
async def recommendation(action: str, monthly: int = 0, days: int = 30) -> dict[str, Any]:
    pol = _load_policy()
    # progi proste: enterprise dla bardzo wysokiego wolumenu, pro dla średniego
    rec = "free"
    if monthly >= 100_000:
        rec = "enterprise"
    elif monthly >= 10_000:
        rec = "pro"
    return {"action": action, "recommended_tier": rec, "tiers": pol.get("tiers", {})}


class SetTierIn(BaseModel):
    tenant: str
    tier: str
    persist: bool | None = None


def _require_admin() -> None:
    if (os.getenv("BILLING_ADMIN") or "").strip() not in {"1", "true", "True"}:
        raise HTTPException(status_code=403, detail="admin required")


@router.post("/admin/set_tier", summary="Admin: set tenant tier (DEV)")
async def admin_set_tier(body: SetTierIn) -> dict[str, Any]:
    _require_admin()
    pol = _load_policy()
    tenants = pol.setdefault("tenants", {})
    tenants[str(body.tenant)] = str(body.tier)
    persisted = bool(body.persist) and (os.getenv("BILLING_POLICY_FILE_WRITE") or "").strip() in {"1", "true", "True"}
    if persisted:
        _save_policy(pol)
    else:
        # zapisz tylko w pamięci
        _POLICY_CACHE = pol
    return {"tenant": body.tenant, "tier": body.tier, "persisted": persisted}


@router.post("/admin/reload", summary="Admin: reload policies from file (DEV)")
async def admin_reload() -> dict[str, bool]:
    _require_admin()
    # Wymuś odczyt z pliku
    path = _policy_file_path()
    if not path.exists():
        _save_policy(_load_policy())
        return {"ok": True}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(raw, dict):
            _save_policy(raw)
    except Exception:
        pass
    return {"ok": True}
