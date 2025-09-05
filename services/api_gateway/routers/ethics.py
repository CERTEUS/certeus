#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/ethics.py              |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/ethics.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla obszaru Equity Meter / HHE.

EN: FastAPI router for Equity Meter / HHE.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, Request
from pydantic import BaseModel

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

class EquityMeterRequest(BaseModel):
    distribution_a: list[float]

    distribution_b: list[float]

class EquityMeterResponse(BaseModel):
    score: float

    deltas: list[float]

class DoubleVerdictRequest(BaseModel):
    W_litera: str

    T_telos: str

    rationale: str | None = None

class DoubleVerdictResponse(BaseModel):
    verdicts: dict

    rationale: str | None = None

# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/ethics.py                        |

# | ROLE: Equity-Meter & HHE (Double-Verdict)                           |

# +=====================================================================+

router = APIRouter(prefix="/v1/ethics", tags=["ethics"])

@router.post("/equity_meter", response_model=EquityMeterResponse)
async def equity_meter(req: EquityMeterRequest, request: Request) -> EquityMeterResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    # Very simple Wasserstein-1 like proxy: average absolute delta

    a, b = req.distribution_a, req.distribution_b

    n = max(len(a), len(b), 1)

    a = (a + [0.0] * (n - len(a)))[:n]

    b = (b + [0.0] * (n - len(b)))[:n]

    deltas = [abs(x - y) for x, y in zip(a, b, strict=False)]

    score = max(0.0, 1.0 - (sum(deltas) / n))

    return EquityMeterResponse(score=round(score, 6), deltas=[round(d, 6) for d in deltas])

@router.post("/double_verdict", response_model=DoubleVerdictResponse)
async def double_verdict(req: DoubleVerdictRequest, request: Request) -> DoubleVerdictResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    return DoubleVerdictResponse(verdicts={"W": req.W_litera, "T": req.T_telos}, rationale=req.rationale)

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
