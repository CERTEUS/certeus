#!/usr/bin/env python3

"""
PL: Router FastAPI dla obszaru interfejs ChatOps.

EN: FastAPI router for ChatOps interface.
"""


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/chatops.py                       |

# | ROLE: ChatOps command router                                        |

# +=====================================================================+

from __future__ import annotations

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel

router = APIRouter(prefix="/v1/chatops", tags=["ChatOps"])


class CommandRequest(BaseModel):
    cmd: str

    args: dict | None = None

    text_context: str | None = None


@router.post("/command")
async def command(req: CommandRequest, request: Request) -> dict:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    # Very small, safe whitelist and synthetic responses

    if req.cmd == "qtm.measure":
        op = (req.args or {}).get("operator", "W")

        return {"dispatched": req.cmd, "args": req.args or {}, "result": {"verdict": op, "p": 0.5}}

    if req.cmd == "cfe.geodesic":
        return {"dispatched": req.cmd, "result": {"path": ["A", "B", "C"], "geodesic_action": 12.34}}

    if req.cmd == "lexqft.tunnel":
        return {"dispatched": req.cmd, "result": {"p_tunnel": 0.7, "min_energy_to_cross": 0.8}}

    raise HTTPException(status_code=400, detail="Unknown or unsupported command")
