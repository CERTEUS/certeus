# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/limits.py                      |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/limits.py                      |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from threading import Lock

from fastapi import HTTPException, Request

# === KONFIGURACJA / CONFIGURATION ===

_DEFAULT_BUDGET = 10_000  # domyślny dzienny budżet jednostek

_TOKEN_BUDGETS: dict[str, int] = {}

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

_LOCK = Lock()

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/limits.py                                |

# | ROLE:                                                               |

# |  PL: Hook limitów per-tenant (QPS/kroki/koszt dowodzenia).          |

# |  EN: Per-tenant limits hook (QPS/steps/proof-cost).                 |

# +=====================================================================+

# | NOTES:                                                              |

# |  - Zero zależności na ".deps": własny get_tenant_id(Request).       |

# |  - Usuwa F841: "tenant" jest realnie użyty (budżet/charge).         |

# +=====================================================================+

__all__ = [
    "enforce_limits",
    "set_tenant_quota",
    "get_tenant_id",
    "get_tenant_balance",
    "allocate_tenant_cost",
    "refund_tenant_units",
]

# In-memory MVP (można później podmienić na Redis/TokenBank)


def get_tenant_id(req: Request) -> str:
    """

    PL: Identyfikacja tenant-a z nagłówka; fallback 'anonymous'.

    EN: Tenant identification from header; fallback to 'anonymous'.

    """

    # typowe nagłówki w Twoim ekosystemie: X-Tenant-ID / X-Org-ID

    tid = req.headers.get("X-Tenant-ID") or req.headers.get("X-Org-ID") or "anonymous"

    return tid


def set_tenant_quota(tenant: str, units: int) -> None:
    """PL: Ustaw budżet jednostek dla tenant-a. EN: Set tenant budget."""

    with _LOCK:
        _TOKEN_BUDGETS[tenant] = max(0, int(units))


def get_tenant_balance(tenant: str) -> int:
    """PL: Zwraca aktualny budżet tenant-a. EN: Return tenant's current budget."""

    with _LOCK:
        return _TOKEN_BUDGETS.get(tenant, _DEFAULT_BUDGET)


def _charge(tenant: str, cost_units: int) -> bool:
    """PL: Pobierz z budżetu; True jeśli wystarczyło. EN: Charge budget."""

    if cost_units <= 0:
        return True  # Operacje o zerowym koszcie zawsze przechodzą.

    with _LOCK:
        cur = _TOKEN_BUDGETS.get(tenant, _DEFAULT_BUDGET)

        if cur < cost_units:
            return False

        _TOKEN_BUDGETS[tenant] = cur - cost_units

        return True


def allocate_tenant_cost(tenant: str, cost_units: int) -> bool:
    """PL/EN: Try charge budget for tenant; returns True if allocated (balance decremented)."""

    return _charge(tenant, cost_units)


def refund_tenant_units(tenant: str, units: int) -> int:
    """PL/EN: Refund units to tenant and return new balance."""

    with _LOCK:
        _TOKEN_BUDGETS[tenant] = _TOKEN_BUDGETS.get(tenant, _DEFAULT_BUDGET) + max(0, int(units))
        return _TOKEN_BUDGETS[tenant]


def enforce_limits(req: Request, *, cost_units: int = 1) -> None:
    """

    PL: Wymuś limity — jeżeli budżet/limity przekroczone, rzuć 429.

    EN: Enforce limits — raise 429 if budget/limits exceeded.

    """

    tenant = get_tenant_id(req)

    # (opcjonalnie) dodatkowe limity: steps/CPU z req.state/metryk — tu hook.

    ok = _charge(tenant, cost_units)

    if not ok:
        raise HTTPException(status_code=429, detail="Rate/Budget limits exceeded")


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
