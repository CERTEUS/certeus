# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/billing/test_token_bank.py                     |
# | ROLE: Project module.                                       |
# | PLIK: tests/billing/test_token_bank.py                     |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Testy jednostkowe dla TokenBank (budżety/żetony dowodów).

EN: Unit tests for TokenBank (proof-cost budgets per tenant).

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import pytest

from billing.proof_token_bank import TokenBank

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

def test_set_and_get_balance() -> None:
    bank = TokenBank()
    bank.set_quota("tenant-a", 10)
    assert bank.balance("tenant-a") == 10

def test_charge_success_and_failure() -> None:
    bank = TokenBank()
    bank.set_quota("t", 5)
    assert bank.charge("t", 3) is True
    assert bank.balance("t") == 2
    # not enough tokens
    assert bank.charge("t", 3) is False
    assert bank.balance("t") == 2

def test_refund_increases_balance() -> None:
    bank = TokenBank()
    bank.refund("t", 4)
    assert bank.balance("t") == 4
    bank.refund("t", 1)
    assert bank.balance("t") == 5

def test_set_quota_clamps_negative() -> None:
    bank = TokenBank()
    bank.set_quota("t", -7)
    assert bank.balance("t") == 0

@pytest.mark.parametrize("amount", [-5, 0])
def test_refund_non_positive_is_noop(amount: int) -> None:
    bank = TokenBank()
    bank.set_quota("t", 1)
    bank.refund("t", amount)
    assert bank.balance("t") == 1

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
