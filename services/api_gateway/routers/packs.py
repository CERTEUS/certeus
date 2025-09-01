#!/usr/bin/env python3

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/packs.py               |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/packs.py               |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from __future__ import annotations

from typing import Any

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel

from packs_core.loader import discover, load as load_pack
from services.api_gateway.limits import enforce_limits

router = APIRouter(prefix="/v1/packs", tags=["packs"])


@router.get("/", summary="List available packs")
async def list_packs() -> list[dict[str, Any]]:
    infos = discover()

    return [{"name": i.name, "abi": i.abi, "capabilities": i.caps} for i in infos]


class HandleRequest(BaseModel):
    pack: str

    kind: str

    payload: dict[str, Any] | None = None


@router.post("/handle", summary="Handle a request using a pack")
async def handle(req: HandleRequest, request: Request) -> dict[str, Any]:
    enforce_limits(request, cost_units=1)

    try:
        pack = load_pack(req.pack)

        result = pack.handle(req.kind, dict(req.payload or {}))

        return {"ok": True, "result": result}

    except Exception as e:  # nosec - błąd pakietu mapujemy na 400
        raise HTTPException(status_code=400, detail=f"pack handle error: {e}") from e
