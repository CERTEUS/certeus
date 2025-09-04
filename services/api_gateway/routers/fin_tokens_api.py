#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/fin_tokens_api.py       |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/fin_tokens_api.py       |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla FIN tokens (request/allocate/status) — stan w pliku,
    ścieżka kontrolowana przez env `CERTEUS_TEST_STATE_PATH` (na potrzeby testów).

EN: FastAPI router for FIN tokens (request/allocate/status) — file-backed state,
    path controlled by env `CERTEUS_TEST_STATE_PATH` (for tests).
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, Field

router = APIRouter(prefix="/v1/fin/tokens", tags=["billing"])


def _state_path() -> Path:
    p = os.getenv("CERTEUS_TEST_STATE_PATH")
    if p:
        return Path(p)
    return Path(__file__).resolve().parents[3] / "data" / "fin_tokens.json"


def _load() -> dict[str, Any]:
    p = _state_path()
    if not p.exists():
        return {"requests": {}}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {"requests": {}}


def _save(state: dict[str, Any]) -> None:
    p = _state_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(state, indent=2, ensure_ascii=False), encoding="utf-8")


class ReqIn(BaseModel):
    user_id: str = Field(min_length=1)
    amount: int = Field(gt=0)
    purpose: str | None = None


class ReqOut(BaseModel):
    request_id: str
    status: str
    user_id: str
    amount: int
    purpose: str | None = None


class AllocIn(BaseModel):
    request_id: str
    allocated_by: str | None = None


class StatusOut(BaseModel):
    request_id: str
    status: str
    allocated_by: str | None = None


@router.post("/request", response_model=ReqOut)
async def request_tokens(req: ReqIn, request: Request) -> ReqOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load()
    import uuid

    rid = uuid.uuid4().hex
    entry = {
        "request_id": rid,
        "status": "PENDING",
        "user_id": req.user_id,
        "amount": int(req.amount),
        "purpose": req.purpose,
        "allocated_by": None,
    }
    state.setdefault("requests", {})[rid] = entry
    _save(state)
    return ReqOut(**entry)


@router.get("/{request_id}", response_model=StatusOut)
async def get_status(request_id: str, request: Request) -> StatusOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load()
    entry = (state.get("requests") or {}).get(request_id)
    if not entry:
        raise HTTPException(status_code=404, detail="unknown request_id")
    return StatusOut(request_id=request_id, status=str(entry.get("status")), allocated_by=entry.get("allocated_by"))


@router.post("/allocate", response_model=StatusOut)
async def allocate(req: AllocIn, request: Request) -> StatusOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    state = _load()
    entry = (state.get("requests") or {}).get(req.request_id)
    if not entry:
        raise HTTPException(status_code=404, detail="unknown request_id")
    entry["status"] = "ALLOCATED"
    if req.allocated_by:
        entry["allocated_by"] = req.allocated_by
    state["requests"][req.request_id] = entry
    _save(state)
    return StatusOut(request_id=req.request_id, status="ALLOCATED", allocated_by=entry.get("allocated_by"))
