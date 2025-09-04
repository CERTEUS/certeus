#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_p2p_queue.py                     |
# | ROLE: P2P queue API tests                                    |
# | PLIK: tests/services/test_p2p_queue.py                     |
# | ROLA: Testy API kolejki P2P                                  |
# +-------------------------------------------------------------+

"""
PL: W8 — testuje enqueue/status/summary/dequeue dla SYNAPSY P2P stub.

EN: W8 — tests enqueue/status/summary/dequeue for SYNAPSY P2P stub.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_p2p_enqueue_and_process_once() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    # Enqueue job
    r = c.post("/v1/p2p/enqueue", json={"device": "hde", "payload": {"case": "W8-P2P"}})
    assert r.status_code == 200
    job_id = r.json().get("job_id")
    assert isinstance(job_id, str)

    # Status should be PENDING
    r = c.get(f"/v1/p2p/jobs/{job_id}")
    assert r.status_code == 200 and r.json().get("status") == "PENDING"

    # Summary has some depth
    r = c.get("/v1/p2p/queue")
    assert r.status_code == 200 and r.json().get("depth") >= 1

    # Dequeue once
    r = c.post("/v1/p2p/dequeue_once")
    assert r.status_code == 200 and r.json().get("status") == "DONE"

    # Status DONE
    r = c.get(f"/v1/p2p/jobs/{job_id}")
    assert r.status_code == 200 and r.json().get("status") == "DONE"
