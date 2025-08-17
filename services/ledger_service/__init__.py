# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/ledger_service/__init__.py     |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                        CERTEUS                              |
# |        Core Engine for Reliable & Unified Systems           |
# +-------------------------------------------------------------+
# ── CERTEUS Project ─────────────────────────────────────────────────────────────
# File: services/ledger_service/__init__.py
# License: Apache-2.0
# Description (PL): Pakiet Ledger – rejestr pochodzenia (chain-of-custody).
# Description (EN): Ledger package – provenance register (chain-of-custody).
# Style Guide: ASCII header, PL/EN docs, labeled code blocks.
# ────────────────────────────────────────────────────────────────

"""
PL: Udostępnia interfejs publiczny: Ledger i LedgerRecord.
EN: Exposes public API: Ledger and LedgerRecord.
"""

# [BLOCK: PUBLIC EXPORTS]
from .ledger import Ledger, LedgerRecord

__all__ = ["Ledger", "LedgerRecord"]
