from kernel.dual_core import z3_adapter, cvc5_adapter
def test_solvers_stub():
    assert z3_adapter.solve([])["status"] == "unsat"
    assert cvc5_adapter.solve([])["status"] == "unsat"
