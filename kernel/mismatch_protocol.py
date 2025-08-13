def detect(z3_res, cvc5_res):
    return z3_res.get("status") != cvc5_res.get("status")
