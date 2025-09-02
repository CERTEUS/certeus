#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/fin.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/fin.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla obszaru FINENITH (quantum alpha).

EN: FastAPI router for FINENITH (quantum alpha).

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class MeasureRequest(BaseModel):
    signals: dict[str, float] | None = None


class MeasureResponse(BaseModel):
    outcome: str

    p: float

    pco: dict | None = None


class UncertaintyResponse(BaseModel):
    lower_bound: float


class EntanglementsResponse(BaseModel):
    pairs: list[tuple[str, str]]

    mi: float


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/fin.py                           |

# | ROLE: FINENITH / "Quantum Alpha" endpoints                          |

# +=====================================================================+

router = APIRouter(prefix="/v1/fin/alpha", tags=["finance"])


@router.post("/measure", response_model=MeasureResponse)
async def measure(req: MeasureRequest, request: Request, response: Response) -> MeasureResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    s = req.signals or {}
    risk = float(sum(v for k, v in s.items() if "risk" in k.lower()))
    sent = float(sum(v for k, v in s.items() if ("sent" in k.lower()) or ("sentiment" in k.lower())))
    score = sent - risk
    outcome = "BUY" if score >= 0 else "SELL"
    p = min(0.95, max(0.05, 0.5 + score / 10.0))

    # Operators R/S are non-commuting in this model; report commutator norm > 0
    comm_norm = 1.0 if (risk != 0.0 or sent != 0.0) else 0.0

    # Build PCO (+ basic DPCO/MCO fields, W12)
    pco = {
        "fin.alpha.measure": {
            "signals": s,
            "operators": {"R": risk, "S": sent, "commutator_RS": comm_norm},
            "outcome": outcome,
            "p": round(p, 6),
            # W12: Data governance fields (minimal)
            "dp_epsilon": 0.5,
            "consent_ref": "consent://demo",
            "lineage": ["io.email.mail_id", "cfe.geodesic_action"],
        }
    }

    # Emit PCO header + metrics + ledger hash
    try:
        import json as _json

        response.headers["X-CERTEUS-PCO-fin.measure"] = _json.dumps(pco["fin.alpha.measure"], separators=(",", ":"))
    except Exception:
        pass
    try:
        from monitoring.metrics_slo import certeus_fin_commutator_rs

        certeus_fin_commutator_rs.set(float(comm_norm))
    except Exception:
        pass
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        doc_hash = "sha256:" + compute_provenance_hash(pco["fin.alpha.measure"], include_timestamp=False)
        ledger_service.record_input(case_id="FIN-ALPHA", document_hash=doc_hash)
    except Exception:
        pass

    return MeasureResponse(outcome=outcome, p=round(p, 6), pco=pco)


@router.get("/uncertainty", response_model=UncertaintyResponse)
async def uncertainty(request: Request) -> UncertaintyResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    return UncertaintyResponse(lower_bound=0.1)


@router.get("/entanglements", response_model=EntanglementsResponse)
async def entanglements(request: Request) -> EntanglementsResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    pairs = [("RISK", "SENTIMENT"), ("BTC", "ETH"), ("GOLD", "USD")]
    mi = 0.12
    try:
        from monitoring.metrics_slo import certeus_fin_entanglement_mi

        for a, b in pairs:
            certeus_fin_entanglement_mi.labels(a=a, b=b).set(mi)
    except Exception:
        pass
    return EntanglementsResponse(pairs=pairs, mi=mi)


@router.get("/operators/commutator")
async def operators_commutator() -> dict[str, float]:
    """PL/EN: Zwraca normę komutatora [R,S] (tu: 1.0 ≠ 0)."""
    try:
        from monitoring.metrics_slo import certeus_fin_commutator_rs

        certeus_fin_commutator_rs.set(1.0)
    except Exception:
        pass
    return {"norm": 1.0}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
