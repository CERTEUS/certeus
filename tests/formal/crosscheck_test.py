#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/formal/crosscheck_test.py                      |
# | ROLE: Z3↔CVC5 cross-check + DRAT/LFSC normalize tests        |
# +-------------------------------------------------------------+

from __future__ import annotations

from hypothesis import given, strategies as st

from core.proofs.cvc5_bridge import solve_and_export_lfsc as cvc5_solve
from core.proofs.normalize import recheck_lfsc, trim_drat
from core.proofs.z3_bridge import solve_and_export_drat as z3_solve


@given(st.integers(min_value=0, max_value=10_000))
def test_crosscheck_simulate_agree_on_status(_n: int) -> None:
    """PL/EN: W trybie simulate obie warstwy zwracają UNSAT → zgodność statusu.

    Keep test portable on CI (no native solver deps).
    """

    z3_res = z3_solve("(assert true)", simulate=True)
    cvc5_res = cvc5_solve("(assert true)", simulate=True)
    assert z3_res.status in {"sat", "unsat", "unknown"}
    assert cvc5_res.status in {"sat", "unsat", "unknown"}
    assert z3_res.status == cvc5_res.status == "unsat"


def test_normalizer_trims_and_deduplicates() -> None:
    raw = """
    c proof header
    1  -2   0
    # comment
    1 -2 0

    3 0
    """.strip()
    out = trim_drat(raw)
    lines = [ln for ln in out.splitlines() if ln]
    assert lines == ["1 -2 0", "3 0"]


def test_lfsc_recheck_stub_accepts_non_empty() -> None:
    assert recheck_lfsc("(check-sat)") is True
    assert recheck_lfsc("") is False
    assert recheck_lfsc(" ") is False
