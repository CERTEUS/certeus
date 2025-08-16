# +-------------------------------------------------------------+
# |                        CERTEUS                              |
# |        Core Engine for Reliable & Unified Systems           |
# +-------------------------------------------------------------+
# ── CERTEUS Project ─────────────────────────────────────────────────────────────
# File: tests/services/test_ledger.py
# License: Apache-2.0
# Description (PL): Testy rejestru pochodzenia (Ledger).
# Description (EN): Tests for the provenance ledger.
# Style Guide: Typed tests, PL/EN docs, labeled blocks.
# ────────────────────────────────────────────────────────────────

"""
PL: Weryfikuje łańcuch parent→child, prefiks 'sha256:' i eksport JSON.
EN: Verifies parent→child chain, 'sha256:' prefix, and JSON export.
"""

# [BLOCK: IMPORTS]
from typing import List
from services.ledger_service import Ledger, LedgerRecord


# [BLOCK: TESTS]
def test_ledger_chain_of_custody():
    # Deterministyczny czas: co wywołanie +1 s
    t = {"now": 1.0}

    def fake_now() -> float:
        t["now"] += 1.0
        return t["now"]

    L = Ledger(now=fake_now)
    a: LedgerRecord = L.record_input(b"doc")
    b: LedgerRecord = L.record_transform(a, b"ocr-out", stage="ocr")
    c: LedgerRecord = L.record_export(b, b"export-docx")

    chain: List[str] = L.ancestry(c.id)
    j: str = L.to_json()

    # [BLOCK: INPUT]
    a: LedgerRecord = L.record_input(b"doc")
    assert a.parent_id is None
    assert a.id.startswith("sha256:")

    # [BLOCK: TRANSFORM]
    b: LedgerRecord = L.record_transform(a, b"ocr-out", stage="ocr")
    c: LedgerRecord = L.record_export(b, b"export-docx")

    # [BLOCK: CHAIN CHECKS]
    assert b.parent_id == a.id and c.parent_id == b.id
    chain: List[str] = L.ancestry(c.id)
    assert chain == [a.id, b.id, c.id]

    # [BLOCK: INTEGRITY]
    assert L.validate_chain() is True
    j: str = L.to_json()
    assert a.id in j and b.id in j and c.id in j
