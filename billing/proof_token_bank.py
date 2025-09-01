# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | FILE: billing/proof_token_bank.py                                   |
# | ROLE:                                                               |
# |  PL: Budżety/żetony na dowodzenie per-tenant.                       |
# |  EN: Proof-cost token budgets per tenant.                           |
# +=====================================================================+

"""PL: In-memory MVP: charge/refund/check; gotowe pod backend Redis. EN: MVP."""

from __future__ import annotations


class TokenBank:
    def __init__(self) -> None:
        self._bal: dict[str, int] = {}

    def set_quota(self, tenant: str, units: int) -> None:
        self._bal[tenant] = max(0, units)

    def charge(self, tenant: str, units: int) -> bool:
        cur = self._bal.get(tenant, 0)
        if cur < units:
            return False
        self._bal[tenant] = cur - units
        return True

    def refund(self, tenant: str, units: int) -> None:
        self._bal[tenant] = self._bal.get(tenant, 0) + max(0, units)

    def balance(self, tenant: str) -> int:
        return self._bal.get(tenant, 0)
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

