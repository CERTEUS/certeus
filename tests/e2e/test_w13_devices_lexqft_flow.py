#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/e2e/test_w13_devices_lexqft_flow.py           |

# | ROLE: Test module.                                          |

# | PLIK: tests/e2e/test_w13_devices_lexqft_flow.py           |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""

PL: E2E przepływ (W13): lexqft coverage → HDE plan → Q‑Oracle → Entangle → Chronosync → Tunnel.

EN: E2E flow (W13): lexqft coverage → HDE plan → Q‑Oracle → Entangle → Chronosync → Tunnel.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

# === TESTY / TESTS ===


def test_w13_devices_lexqft_flow() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    # 1) lexqft coverage reset + update + state
    r = c.post("/v1/lexqft/coverage/reset")
    assert r.status_code == 200

    payload = [
        {"gamma": 0.93, "weight": 1.0, "uncaptured": 0.03},
        {"gamma": 0.97, "weight": 2.0, "uncaptured": 0.01},
    ]
    r = c.post("/v1/lexqft/coverage/update", json=payload)
    assert r.status_code == 200 and r.json().get("ok") is True

    r = c.get("/v1/lexqft/coverage/state")
    assert r.status_code == 200
    state = r.json()
    assert 0.0 <= float(state["coverage_gamma"]) <= 1.0
    assert 0.0 <= float(state["uncaptured_mass"]) <= 1.0

    # 2) Devices: HDE plan
    r = c.post("/v1/devices/horizon_drive/plan", json={"case": "D13", "target_horizon": 0.30})
    assert r.status_code == 200
    hde = r.json()
    assert hde.get("best_strategy") in {"balanced", "aggressive"}
    assert isinstance(hde.get("alternatives"), list) and len(hde["alternatives"]) >= 2

    # 3) Devices: Q‑Oracle expectation (constraints influence)
    r = c.post(
        "/v1/devices/qoracle/expectation",
        json={"question": "maximize expected payoff?", "constraints": {"budget": 120}},
    )
    assert r.status_code == 200
    q = r.json()
    assert "optimum" in q and isinstance(q.get("distribution"), list)
    ps = [float(x["p"]) for x in q["distribution"]]
    assert all(0.0 <= p <= 1.0 for p in ps)
    assert abs(max(ps) - float(q.get("payoff", 0.0))) <= 1e-6

    # 4) Devices: Entangle
    r = c.post("/v1/devices/entangle", json={"variables": ["X", "Y"], "target_negativity": 0.2})
    assert r.status_code == 200
    ent = r.json()
    assert isinstance(ent.get("certificate"), str)
    assert 0.0 <= float(ent.get("achieved_negativity", 0.0)) <= 0.12

    # 5) Devices: Chronosync
    r = c.post(
        "/v1/devices/chronosync/reconcile",
        json={"coords": {"node": "A"}, "pc_delta": {"doc": "+hash"}},
    )
    assert r.status_code == 200
    cs = r.json()
    assert cs.get("reconciled") is True
    assert isinstance(cs.get("sketch", {}).get("treaty", {}), dict)

    # 6) lexqft tunnel + PCO headers present
    r = c.post("/v1/lexqft/tunnel", json={"state_uri": "lexqft-case-1", "evidence_energy": 1.2})
    assert r.status_code == 200
    t = r.json()
    assert 0.5 <= float(t["p_tunnel"]) <= 0.95
    # PCO headers from response
    hdrs = r.headers
    assert "X-CERTEUS-PCO-qlaw.tunneling.p" in hdrs
    assert "X-CERTEUS-PCO-qlaw.tunneling.path" in hdrs
    assert "X-CERTEUS-PCO-qlaw.tunneling.min_energy" in hdrs
