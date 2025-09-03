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
