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
PL: Router FastAPI – Billing & Cost‑tokens (budżety, refund, alokacje).

EN: FastAPI router – Billing & Cost‑tokens (budgets, refund, allocations).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, Request
from pydantic import BaseModel, Field

from services.api_gateway import limits as _limits
from services.api_gateway.limits import (
    get_tenant_balance,
    get_tenant_id,
    refund_tenant_units,
    set_tenant_quota,
)

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===


class QuotaRequest(BaseModel):
    tenant: str
    units: int = Field(..., ge=0)


class RefundRequest(BaseModel):
    tenant: str
    units: int = Field(..., ge=1)


class AllocateRequest(BaseModel):
    units: int = Field(..., ge=1, description="Units to add to current tenant budget")


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/billing", tags=["billing"])

# Szacunkowe koszty akcji (jednostki budżetu)
_COST_TABLE: dict[str, int] = {
    "qtm.measure": 1,
    "qtm.decoherence": 1,
    "system.analyze": 3,
    "ingest.upload": 2,
    "lexqft.tunnel": 2,
    "proofgate.publish": 5,
}


class EstimateRequest(BaseModel):
    action: str = Field(..., description="Action key, e.g. qtm.measure")


@router.post("/estimate", summary="Estimate cost units for an action")
def estimate(request: Request, body: EstimateRequest) -> dict[str, int | str]:
    """PL: Zwraca szacunkowy koszt jednostek dla podanej akcji.

    EN: Returns estimated unit cost for a given action.
    """
    tenant = get_tenant_id(request)
    base = int(_COST_TABLE.get(body.action, 1))
    tier = _limits.get_tenant_tier(tenant)
    return {"tenant": tenant, "tier": tier, "action": body.action, "estimated_units": base}


@router.get(
    "/recommendation",
    summary="Recommend tier based on action and monthly volume",
    description=(
        "Provide a simple recommendation given an action key and a monthly volume. "
        "Computes required daily units = units_per_request * (monthly / days)."
    ),
)
def recommendation(
    request: Request,
    action: str,
    monthly: int = 1000,
    days: int = 30,
) -> dict[str, object]:
    tenant = get_tenant_id(request)
    tier_cur = _limits.get_tenant_tier(tenant)
    units_per_req = int(_COST_TABLE.get(action, 1))
    daily_calls = max(1.0, float(monthly) / max(1, days))
    req_daily_units = int(units_per_req * daily_calls)

    pol = _limits._load_policies()  # type: ignore[attr-defined]
    tiers = pol.get("tiers", {}) if isinstance(pol, dict) else {}
    ranked: list[tuple[str, int]] = []
    if isinstance(tiers, dict):
        for name, cfg in tiers.items():
            if isinstance(cfg, dict):
                dq = cfg.get("daily_quota")
                if isinstance(dq, (int, float)):
                    ranked.append((str(name), int(dq)))
    ranked.sort(key=lambda x: x[1])
    rec: str | None = None
    for name, dq in ranked:
        if dq >= req_daily_units:
            rec = name
            break
    rec = rec or (ranked[-1][0] if ranked else "free")
    upgrade_needed = rec != tier_cur
    return {
        "tenant": tenant,
        "tier_current": tier_cur,
        "action": action,
        "units_per_request": units_per_req,
        "monthly_calls": int(monthly),
        "days": int(days),
        "required_daily_units": req_daily_units,
        "recommended_tier": rec,
        "upgrade_needed": upgrade_needed,
        "tiers": [{"name": n, "daily_quota": q} for (n, q) in ranked],
    }


# --- ADMIN (DEV) --------------------------------------------------------------


class AdminSetTierRequest(BaseModel):
    tenant: str
    tier: str
    persist: bool = Field(default=False, description="Persist changes to policy file if allowed")


@router.post("/admin/set_tier", summary="[DEV] Map tenant to tier")
def admin_set_tier(req: AdminSetTierRequest) -> dict[str, object]:
    import os

    from fastapi import HTTPException

    if (os.getenv("BILLING_ADMIN") or "").strip() not in {"1", "true", "True"}:
        raise HTTPException(status_code=403, detail="Admin disabled")
    return _limits.set_tenant_tier_policy(req.tenant, req.tier, persist=req.persist)


@router.post("/admin/reload", summary="[DEV] Reload billing policies from file")
def admin_reload() -> dict[str, object]:
    import os

    from fastapi import HTTPException

    if (os.getenv("BILLING_ADMIN") or "").strip() not in {"1", "true", "True"}:
        raise HTTPException(status_code=403, detail="Admin disabled")
    _limits.reload_policies()
    pol = _limits._load_policies()  # type: ignore[attr-defined]
    return {"reloaded": True, "tiers": list((pol.get("tiers") or {}).keys())}


@router.post("/quota", summary="Set tenant quota")
def set_quota(req: QuotaRequest) -> dict[str, int | str]:
    """PL: Ustaw całkowity budżet jednostek (quota) dla wskazanego tenant-a.

    EN: Set total unit budget (quota) for the given tenant.
    """
    set_tenant_quota(req.tenant, req.units)
    return {"tenant": req.tenant, "balance": get_tenant_balance(req.tenant)}


@router.get("/balance", summary="Get current balance")
def balance(request: Request) -> dict[str, int | str]:
    """PL: Zwraca bieżący stan budżetu dla tenant-a z nagłówka X-Tenant-ID.

    EN: Returns current budget balance for the tenant from X-Tenant-ID header.
    """
    tenant = get_tenant_id(request)
    return {"tenant": tenant, "balance": get_tenant_balance(tenant)}


@router.post("/refund", summary="Refund units to tenant budget")
def refund(req: RefundRequest) -> dict[str, int | str]:
    """PL: Zwraca (dodaje) jednostki do budżetu wskazanego tenant-a.

    EN: Refunds (adds) units back to the given tenant budget.
    """
    refund_tenant_units(req.tenant, req.units)
    return {"tenant": req.tenant, "balance": get_tenant_balance(req.tenant)}


@router.post("/allocate", summary="Allocate units to current tenant (PENDING → allocate)")
def allocate(request: Request, req: AllocateRequest) -> dict[str, int | str]:
    """PL: Doładowuje jednostki do budżetu tenant-a z nagłówka (PENDING→allocate).

    EN: Allocates units to current tenant (PENDING→allocate use-case).
    """
    tenant = get_tenant_id(request)
    refund_tenant_units(tenant, req.units)
    return {"tenant": tenant, "balance": get_tenant_balance(tenant)}


@router.get("/policies", summary="Get billing policies (tiers/tenants)")
def get_policies() -> dict[str, object]:
    """PL: Zwraca aktualne polityki billing (tiers/tenants) — tylko odczyt.

    EN: Returns current billing policies (tiers/tenants) — read‑only.
    """

    # Bez bezpośrednich referencji do pliku — korzystamy z loadera w limits
    pol = _limits._load_policies()  # type: ignore[attr-defined]
    # Sanitization: upewnijmy się, że to dict z dozwolonymi kluczami
    out: dict[str, object] = {}
    try:
        if isinstance(pol, dict):
            tiers = pol.get("tiers")
            tenants = pol.get("tenants")
            if isinstance(tiers, dict):
                out["tiers"] = tiers
            if isinstance(tenants, dict):
                out["tenants"] = tenants
    except Exception:
        pass
    return out


@router.get("/tenant_tier", summary="Get current tenant tier")
def tenant_tier(request: Request) -> dict[str, str]:
    """PL: Zwraca tier tenant‑a wynikający z polityk.

    EN: Returns the tenant tier according to policies.
    """

    tenant = get_tenant_id(request)
    tier = _limits.get_tenant_tier(tenant)
    return {"tenant": tenant, "tier": tier}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
