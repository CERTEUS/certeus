#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/chatops.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/chatops.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla obszaru interfejs ChatOps.

EN: FastAPI router for ChatOps interface.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, HTTPException, Request, Response
from pydantic import BaseModel

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class CommandRequest(BaseModel):
    cmd: str

    args: dict | None = None

    text_context: str | None = None


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/chatops.py                       |

# | ROLE: ChatOps command router                                        |

# +=====================================================================+

router = APIRouter(prefix="/v1/chatops", tags=["ChatOps"])


@router.post("/command")
async def command(req: CommandRequest, request: Request) -> dict:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    # Very small, safe whitelist and synthetic responses

    if req.cmd == "qtm.measure":
        # Bridge to QTMP measure endpoint to ensure PCO/ledger behavior
        try:
            from services.api_gateway.routers import qtm as _qtm

            args = req.args or {}
            op = str(args.get("operator", "W"))
            case = str(args.get("case") or args.get("source") or "chatops-case")
            mreq = _qtm.MeasureRequest(
                operator=op, source=f"chatops:{req.cmd}", case=case
            )
            tmp_resp = Response()
            out = await _qtm.measure(mreq, request, tmp_resp)
            # Expose essential PCO headers (collapse event, priorities, etc.)
            pco_headers = {
                k: v
                for k, v in tmp_resp.headers.items()
                if k.startswith("X-CERTEUS-PCO-")
            }
            return {
                "dispatched": req.cmd,
                "args": args,
                "result": out.model_dump(),
                "pco": pco_headers,
            }
        except Exception as e:  # pragma: no cover
            raise HTTPException(
                status_code=500, detail=f"qtm.measure failed: {e}"
            ) from e

    if req.cmd == "cfe.geodesic":
        return {
            "dispatched": req.cmd,
            "result": {"path": ["A", "B", "C"], "geodesic_action": 12.34},
        }

    if req.cmd == "lexqft.tunnel":
        return {
            "dispatched": req.cmd,
            "result": {"p_tunnel": 0.7, "min_energy_to_cross": 0.8},
        }

    raise HTTPException(status_code=400, detail="Unknown or unsupported command")


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
