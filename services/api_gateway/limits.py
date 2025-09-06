# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/limits.py                      |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/limits.py                      |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Limity i budżety per-tenant (Proof-Cost tokens) z wsparciem prostych
    polityk cennikowych (tiering) z pliku JSON. Fallback do stałych domyślnych,
    jeżeli plik polityk nie jest dostępny.

EN: Per-tenant limits and budgets (Proof-Cost tokens) with simple pricing
    policies (tiering) loaded from a JSON file. Falls back to static defaults
    when the policy file is not available.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path
from threading import Lock

from fastapi import HTTPException, Request

# === KONFIGURACJA / CONFIGURATION ===

_DEFAULT_BUDGET = 10_000  # domyślny dzienny budżet jednostek

_TOKEN_BUDGETS: dict[str, int] = {}

# Polityki billing (tiering) – ładowane best‑effort z JSON
_POLICY_CACHE: dict[str, object] | None = None
_POLICY_LOCK: Lock = Lock()


def _policy_path() -> Path:
    """Zwróć ścieżkę do pliku polityk (ENV lub domyślnie runtime/billing/policies.json)."""

    root = Path(__file__).resolve().parents[2]
    default = root / "runtime" / "billing" / "policies.json"
    env = os.getenv("BILLING_POLICY_FILE")
    return Path(env) if env else default


def _load_policies() -> dict[str, object]:
    """Wczytaj polityki z JSON (jeśli brak – struktura domyślna)."""

    global _POLICY_CACHE
    if _POLICY_CACHE is not None:
        return _POLICY_CACHE

    # Domyślne polityki (free/pro/enterprise)
    default_policies: dict[str, object] = {
        "tiers": {
            "free": {"daily_quota": 200, "burst": 1.0},
            "pro": {"daily_quota": 10_000, "burst": 2.0},
            "enterprise": {"daily_quota": 250_000, "burst": 3.0},
        },
        "tenants": {
            "anonymous": "free",
        },
    }

    try:
        p = _policy_path()
        if p.exists():
            data = json.loads(p.read_text(encoding="utf-8"))
            if isinstance(data, dict) and "tiers" in data:
                _POLICY_CACHE = data  # type: ignore[assignment]
            else:
                _POLICY_CACHE = default_policies
        else:
            _POLICY_CACHE = default_policies
    except Exception:
        _POLICY_CACHE = default_policies

    return _POLICY_CACHE


def get_tenant_tier(tenant: str) -> str:
    """Zwróć tier tenant‑a wg polityk (default: free)."""

    pol = _load_policies()
    tenants = pol.get("tenants", {}) if isinstance(pol, dict) else {}
    if isinstance(tenants, dict):
        t = tenants.get(tenant)
        if isinstance(t, str) and t:
            return t
    return "free"


def _default_budget_for(tenant: str) -> int:
    """Budżet domyślny wg tier‑u (jeśli brak ekspl. ustawienia)."""

    pol = _load_policies()
    tiers = pol.get("tiers", {}) if isinstance(pol, dict) else {}
    tier = get_tenant_tier(tenant)
    if isinstance(tiers, dict):
        t = tiers.get(tier)
        if isinstance(t, dict):
            dq = t.get("daily_quota")
            if isinstance(dq, int | float):
                try:
                    return max(0, int(dq))
                except Exception:
                    pass
    # fallback stały
    return _DEFAULT_BUDGET


def reload_policies() -> None:
    """Wyczyść cache i przeładuj polityki z pliku."""

    global _POLICY_CACHE
    with _POLICY_LOCK:
        _POLICY_CACHE = None
        _ = _load_policies()


def set_tenant_tier_policy(tenant: str, tier: str, *, persist: bool = False) -> dict[str, object]:
    """Ustaw mapowanie tenant→tier w politykach. Opcjonalnie zapisz do pliku.

    Zwraca wynik z polami: tenant, tier, persisted (bool), policy_path (opcjonalnie).
    """

    pol = _load_policies()
    if not (isinstance(pol, dict) and isinstance(pol.get("tiers"), dict)):
        raise ValueError("Invalid billing policies structure")
    if tier not in pol["tiers"]:  # type: ignore[index]
        raise ValueError(f"Unknown tier: {tier}")

    with _POLICY_LOCK:
        tmap = pol.setdefault("tenants", {})  # type: ignore[assignment]
        if not isinstance(tmap, dict):
            raise ValueError("Invalid tenants map in policies")
        tmap[str(tenant)] = str(tier)

        persisted = False
        pth: str | None = None
        want_write = persist or (os.getenv("BILLING_POLICY_FILE_WRITE") in {"1", "true", "True"})
        if want_write:
            try:
                p = _policy_path()
                p.write_text(
                    json.dumps(pol, ensure_ascii=False, indent=2, sort_keys=True),
                    encoding="utf-8",
                )
                persisted = True
                pth = str(p)
            except Exception:
                persisted = False
                pth = None

    return {
        "tenant": tenant,
        "tier": tier,
        "persisted": persisted,
        "policy_path": pth or "",
    }


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
