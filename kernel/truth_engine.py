from .dual_core import z3_adapter, cvc5_adapter
from . import mismatch_protocol

def verify(assumptions):
    z3_res = z3_adapter.solve(assumptions)
    cvc5_res = cvc5_adapter.solve(assumptions)
    mismatch = mismatch_protocol.detect(z3_res, cvc5_res)
    return {"z3": z3_res, "cvc5": cvc5_res, "mismatch": mismatch}
