#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/p2p.py                  |
# | ROLE: P2P queue API (stub)                                   |
# | PLIK: services/api_gateway/routers/p2p.py                  |
# | ROLA: API kolejki P2P (stub)                                 |
# +-------------------------------------------------------------+

"""
PL: Router FastAPI — SYNAPSY P2P v1 (stub): enqueue/status/summary/dequeue.

EN: FastAPI router — SYNAPSY P2P v1 (stub): enqueue/status/summary/dequeue.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from typing import Any

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, Field

from runtime.p2p_queue import P2P_QUEUE
from runtime.p2p_transport import echo_roundtrip
from services.api_gateway.limits import enforce_limits, get_tenant_id

# === MODELE / MODELS ===


class EnqueueRequest(BaseModel):
    device: str = Field(pattern=r"^(hde|qoracle|entangler|chronosync)$")
    payload: dict[str, Any] | None = None


class EnqueueResponse(BaseModel):
    job_id: str
    status: str
    eta_hint: str


class JobStatusResponse(BaseModel):
    job_id: str
    status: str
    device: str
    payload: dict[str, Any] | None = None


class QueueSummaryResponse(BaseModel):
    depth: int
    by_device: dict[str, int]


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/p2p", tags=["p2p"])


@router.post("/enqueue", response_model=EnqueueResponse)
async def enqueue(req: EnqueueRequest, request: Request) -> EnqueueResponse:
    enforce_limits(request, cost_units=1)
    tenant = get_tenant_id(request)
    j = P2P_QUEUE.enqueue(
        tenant=tenant, device=req.device, payload=dict(req.payload or {})
    )
    return EnqueueResponse(job_id=j.id, status=j.status, eta_hint=j.eta_hint)


@router.get("/jobs/{job_id}", response_model=JobStatusResponse)
async def job_status(job_id: str, request: Request) -> JobStatusResponse:
    enforce_limits(request, cost_units=1)
    j = P2P_QUEUE.status(job_id)
    if not j:
        raise HTTPException(status_code=404, detail="job not found")
    return JobStatusResponse(
        job_id=j.id, status=j.status, device=j.device, payload=j.payload
    )


@router.get("/queue", response_model=QueueSummaryResponse)
async def queue_summary(request: Request) -> QueueSummaryResponse:
    enforce_limits(request, cost_units=1)
    s = P2P_QUEUE.summary()
    return QueueSummaryResponse(
        depth=int(s.get("depth", 0)), by_device=dict(s.get("by_device", {}))
    )


@router.post("/dequeue_once", response_model=JobStatusResponse)
async def dequeue_once(request: Request) -> JobStatusResponse:
    """PL: Jednorazowo przetwarza pierwsze oczekujące zlecenie (do testów).

    EN: Processes the first pending job once (for tests).
    """

    enforce_limits(request, cost_units=1)
    j = P2P_QUEUE.dequeue_once()
    if not j:
        raise HTTPException(status_code=404, detail="no pending jobs")
    return JobStatusResponse(
        job_id=j.id, status=j.status, device=j.device, payload=j.payload
    )


@router.get("/transport/echo")
async def transport_echo(msg: str = "synapse") -> dict[str, object]:
    """PL/EN: Echo-check the in-memory transport stub (report-only utility)."""
    rep = echo_roundtrip(msg)
    rep["message"] = msg
    return rep


@router.get("/transport/echo")
async def transport_echo(msg: str = "synapse") -> dict[str, object]:
    """PL/EN: Echo-check the in-memory transport stub (report-only utility)."""
    rep = echo_roundtrip(msg)
    rep["message"] = msg
    return rep


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
