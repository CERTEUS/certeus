#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_qtm_property.py                  |

# | ROLE: Test module.                                          |

# | PLIK: tests/services/test_qtm_property.py                  |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Własnościowe testy sekwencji QTM — normalizacja i UB.

EN: Property-based tests of QTM sequences — normalization and UB bounds.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient
from hypothesis import HealthCheck, given, settings, strategies as st
from hypothesis.strategies import composite


def _norm(dist: list[float]) -> list[float]:
    s = sum(max(0.0, x) for x in dist) or 1.0
    return [max(0.0, x) / s for x in dist]


ops_strategy = st.lists(st.sampled_from(["L", "T", "W", "I", "C"]), min_size=1, max_size=5)


@composite
def basis_and_dist(draw):
    n = draw(st.integers(min_value=2, max_value=3))
    perm = draw(st.permutations(["ALLOW", "DENY", "ABSTAIN"]))
    basis = list(perm[:n])
    dist = draw(
        st.lists(
            st.floats(min_value=0, max_value=10, allow_nan=False, allow_infinity=False), min_size=n, max_size=n
        ).filter(lambda xs: sum(xs) > 0)
    )
    return basis, dist


@settings(max_examples=30, suppress_health_check=[HealthCheck.too_slow])
@given(bd=basis_and_dist(), ops=ops_strategy)
def test_qtm_sequence_property_holds(bd: tuple[list[str], list[float]], ops: list[str]) -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    basis, dist = bd
    dist = _norm(dist)
    r = c.post("/v1/qtm/state", json={"case": "HPROP", "basis": basis, "probs": dist})
    assert r.status_code == 200
    r2 = c.post("/v1/qtm/measure_sequence", json={"case": "HPROP", "operators": ops})
    assert r2.status_code == 200
    js = r2.json()
    # steps length equals operators length
    assert len(js.get("steps", [])) == len(ops)
    # UB bound within [0,1]
    ub = float(js.get("uncertainty_bound", {}).get("L_T", 0.0))
    assert 0.0 <= ub <= 1.0
