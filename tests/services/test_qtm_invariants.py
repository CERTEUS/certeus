#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_qtm_invariants.py                |

# | ROLE: Test module.                                          |

# | PLIK: tests/services/test_qtm_invariants.py                |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Testy inwariantów QTM — zakresy UB i wartości oczekiwań.

EN: QTM invariants tests — UB ranges and expectation values.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

# === TESTY / TESTS ===

def test_qtm_sequence_uncertainty_and_probs_bounds() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    case = "INV-QTMP"
    # Set explicit state with valid distribution
    r = c.post(
        "/v1/qtm/state",
        json={"case": case, "basis": ["ALLOW", "DENY", "ABSTAIN"], "probs": [0.5, 0.3, 0.2]},
    )
    assert r.status_code == 200
    # Measure sequence
    r2 = c.post("/v1/qtm/measure_sequence", json={"case": case, "operators": ["L", "T", "W"]})
    assert r2.status_code == 200
    body = r2.json()
    ub = body.get("uncertainty_bound", {})
    val = float(ub.get("L_T", 0.0))
    assert 0.0 <= val <= 1.0

def test_qtm_expectation_in_range() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    case = "INV-EXP"
    c.post(
        "/v1/qtm/state",
        json={"case": case, "basis": ["ALLOW", "DENY", "ABSTAIN"], "probs": [0.6, 0.2, 0.2]},
    )
    r = c.post("/v1/qtm/expectation", json={"case": case, "operator": "W"})
    assert r.status_code == 200
    v = float(r.json().get("value", 0.0))
    assert 0.0 <= v <= 1.0
