#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: runtime/p2p_queue.py                                          |
# | ROLE:                                                                |
# |  PL: Minimalna, deterministyczna kolejka P2P (stub, in-proc).       |
# |  EN: Minimal deterministic P2P queue (in-proc stub).                 |
# +=====================================================================+

"""
PL: Prosty stub P2P do kolejkowania zadań Devices (HDE/Q-Oracle/Entangler...).
    Zapewnia `enqueue`, `status`, `summary` i `dequeue_once` (do testów).

EN: Simple P2P stub for queuing device jobs. Provides `enqueue`, `status`,
    `summary`, and `dequeue_once` (for tests).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from dataclasses import dataclass
import time
from typing import Any


@dataclass(slots=True)
class P2PJob:
    id: str
    tenant: str
    device: str
    payload: dict[str, Any]
    status: str
    enqueued_at: float
    eta_hint: str


class P2PQueue:
    def __init__(self) -> None:
        self._jobs: dict[str, P2PJob] = {}
        self._order: list[str] = []

    def enqueue(self, tenant: str, device: str, payload: dict[str, Any]) -> P2PJob:
        now = time.time()
        jid = f"p2p_{int(now * 1000)}_{device}"
        job = P2PJob(
            id=jid,
            tenant=tenant,
            device=device,
            payload=dict(payload),
            status="PENDING",
            enqueued_at=now,
            eta_hint="~1–5m",
        )
        self._jobs[jid] = job
        self._order.append(jid)
        try:
            # metrics (best-effort)
            from monitoring.metrics_slo import (
                certeus_p2p_enqueued_total,
                certeus_p2p_queue_depth,
            )

            certeus_p2p_enqueued_total.labels(device=device).inc()
            certeus_p2p_queue_depth.set(len(self._order))
        except Exception:
            pass
        return job

    def status(self, job_id: str) -> P2PJob | None:
        return self._jobs.get(job_id)

    def summary(self) -> dict[str, Any]:
        by_device: dict[str, int] = {}
        for jid in self._order:
            j = self._jobs.get(jid)
            if not j or j.status != "PENDING":
                continue
            by_device[j.device] = 1 + by_device.get(j.device, 0)
        return {"depth": len(self._order), "by_device": by_device}

    def dequeue_once(self) -> P2PJob | None:
        # Pop first pending and mark done (simulate remote processing)
        while self._order:
            jid = self._order.pop(0)
            job = self._jobs.get(jid)
            if job and job.status == "PENDING":
                job.status = "DONE"
                try:
                    from monitoring.metrics_slo import (
                        certeus_p2p_dequeued_total,
                        certeus_p2p_queue_depth,
                    )

                    certeus_p2p_dequeued_total.labels(device=job.device).inc()
                    certeus_p2p_queue_depth.set(len(self._order))
                except Exception:
                    pass
                return job
        return None


P2P_QUEUE = P2PQueue()
