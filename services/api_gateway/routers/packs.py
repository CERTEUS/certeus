#!/usr/bin/env python3
from __future__ import annotations

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel

from packs_core.loader import discover, load as load_pack

router = APIRouter(prefix="/v1/packs", tags=["packs"])


@router.get("")
async def list_packs() -> list[dict[str, object]]:
    infos = discover()
    return [{"name": i.name, "abi": i.abi, "capabilities": i.caps} for i in infos]


class HandleRequest(BaseModel):
    pack: str
    kind: str
    payload: dict | None = None


@router.post("/handle")
async def handle(req: HandleRequest, request: Request) -> dict:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    path = req.pack
    kind = req.kind
    payload = req.payload or {}
    try:
        pack = load_pack(path)
        result = pack.handle(kind, dict(payload))
        return {"ok": True, "result": result}
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"pack handle error: {e}") from e
