#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_devices_v02.py                   |

# | ROLE: Test module.                                          |

# | PLIK: tests/services/test_devices_v02.py                   |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Testy usług urządzeń (v0.2): planowanie, oczekiwania i metryki.

EN: Device services (v0.2) tests: planning, expectations and metrics.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

# === TESTY / TESTS ===


def test_hde_plan_alternatives_and_best() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post("/v1/devices/horizon_drive/plan", json={"case": "D13", "target_horizon": 0.25})
    assert r.status_code == 200
    js = r.json()
    assert isinstance(js.get("alternatives"), list) and len(js["alternatives"]) >= 2
    assert js.get("best_strategy") in {"balanced", "aggressive"}
    # chosen plan fields
    assert isinstance(js.get("cost_tokens"), int)
    assert isinstance(js.get("expected_kappa"), float)


def test_qoracle_generalized_question_distribution() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post("/v1/devices/qoracle/expectation", json={"question": "Should we appeal?"})
    assert r.status_code == 200
    js = r.json()
    assert "optimum" in js and isinstance(js["distribution"], list)
    ps = [float(x["p"]) for x in js["distribution"]]
    assert all(0.0 <= p <= 1.0 for p in ps)


def test_entangle_negativity_metric_and_bounds() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post("/v1/devices/entangle", json={"variables": ["X", "Y"], "target_negativity": 0.2})
    assert r.status_code == 200
    val = float(r.json().get("achieved_negativity", 0.0))
    assert 0.0 <= val <= 0.12


def test_chronosync_default_clauses_present() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post(
        "/v1/devices/chronosync/reconcile",
        json={"coords": {"A": 1}, "pc_delta": {"B": 2}},
    )
    assert r.status_code == 200
    clauses = r.json().get("sketch", {}).get("treaty", {}).get("clauses")
    assert isinstance(clauses, dict) and "arbitration" in clauses
