#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/lexqft.py              |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/lexqft.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Router FastAPI dla obszaru lexqft / geometria sensu.



EN: FastAPI router for lexqft / geometry of meaning.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===
class TunnelRequest(BaseModel):
    state_uri: str | None = None

    barrier_model: dict | None = None

    evidence_energy: float = Field(ge=0)


class TunnelResponse(BaseModel):
    p_tunnel: float

    min_energy_to_cross: float

    path: list[str]


# === LOGIKA / LOGIC ===


# +=====================================================================+


# |                              CERTEUS                                |


# +=====================================================================+


router = APIRouter(prefix="/v1/lexqft", tags=["lexqft"])


# | FILE: services/api_gateway/routers/lexqft.py                        |


# | ROLE: lexqft endpoints (evidence tunneling)                         |


# +=====================================================================+


class CoverageResponse(BaseModel):
    coverage_gamma: float


@router.get("/coverage", response_model=CoverageResponse)
async def coverage() -> CoverageResponse:
    """PL/EN: Telemetria lexqft (stub) – gamma pokrycia."""
    return CoverageResponse(coverage_gamma=0.953)


@router.post("/tunnel", response_model=TunnelResponse)
async def tunnel(req: TunnelRequest, request: Request, response: Response) -> TunnelResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    # Placeholder physics: if energy > 1.0, tunneling is almost certain.

    e = req.evidence_energy

    p = 0.95 if e >= 1.0 else max(0.05, e * 0.6)

    min_e = 0.8

    path = ["start", "barrier", "post-barrier"] if p > 0.5 else ["start", "reflect"]
    resp = TunnelResponse(p_tunnel=round(p, 6), min_energy_to_cross=min_e, path=path)

    # PCO headers: qlaw.tunneling.*
    try:
        response.headers["X-CERTEUS-PCO-qlaw.tunneling.p"] = str(resp.p_tunnel)
        response.headers["X-CERTEUS-PCO-qlaw.tunneling.path"] = "/".join(path)
        response.headers["X-CERTEUS-PCO-qlaw.tunneling.min_energy"] = str(min_e)
    except Exception:
        pass

    # Record to Ledger (hash of tunneling outcome)
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        payload = {"qlaw.tunneling": {"p": resp.p_tunnel, "path": path, "min_energy": min_e}}
        doc_hash = "sha256:" + compute_provenance_hash(payload, include_timestamp=False)
        case_id = req.state_uri or "lexqft-case"
        ledger_service.record_input(case_id=case_id, document_hash=doc_hash)
    except Exception:
        pass

    return resp


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
