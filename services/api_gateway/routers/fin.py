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


# --- Pilot W16: strategie Q-Alpha — symulacja i PnL ---


class SimulateRequest(BaseModel):
    strategy_id: str
    capital: float = 100_000.0
    horizon_days: int = 30
    params: dict[str, float] | None = None


class SimulateResponse(BaseModel):
    strategy_id: str
    capital_start: float
    capital_end: float
    pnl_abs: float
    pnl_pct: float
    sharpe_stub: float
    pco: dict | None = None


class PnLResponse(BaseModel):
    tenant: str
    runs: list[SimulateResponse]


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/fin.py                           |

# | ROLE: FINENITH / "Quantum Alpha" endpoints                          |

# +=====================================================================+

router = APIRouter(prefix="/v1/fin/alpha", tags=["finance"])

# Per-tenant pamięć krótkoterminowa (ostatnie symulacje)
_FIN_RUNS: dict[str, list[SimulateResponse]] = {}


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


@router.post("/simulate", response_model=SimulateResponse)
async def simulate(req: SimulateRequest, request: Request, response: Response) -> SimulateResponse:
    """
    PL: Symulacja 2 strategii Q-Alpha (stub): qalpha-momentum, qalpha-arb.
    EN: Simulate 2 Q-Alpha strategies (stub): qalpha-momentum, qalpha-arb.
    """
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=3)

    strat = req.strategy_id.lower().strip()
    cap0 = float(req.capital)
    days = max(1, int(req.horizon_days))

    # Deterministyczne stopy zwrotu (stub)
    if strat in {"qalpha-momentum", "momentum"}:
        daily = 0.0008  # ~0.08% dziennie
        vol = 0.004
    elif strat in {"qalpha-arb", "arb", "arbitrage"}:
        daily = 0.0005
        vol = 0.001
    else:
        daily = 0.0003
        vol = 0.002

    # Prosty model: cap_T = cap0 * (1 + daily)^days; Sharpe stub = daily/vol*sqrt(252)
    capT = cap0 * ((1.0 + daily) ** days)
    pnl_abs = capT - cap0
    pnl_pct = (capT / cap0) - 1.0
    sharpe = (daily / max(1e-9, vol)) * (252**0.5)

    pco = {
        "fin.alpha.simulation": {
            "strategy": strat,
            "capital_start": round(cap0, 2),
            "capital_end": round(capT, 2),
            "horizon_days": days,
            "params": req.params or {},
            "metrics": {"pnl_abs": round(pnl_abs, 2), "pnl_pct": round(pnl_pct, 6), "sharpe_stub": round(sharpe, 3)},
        }
    }

    # Nagłówek PCO i metryki
    try:
        import json as _json

        response.headers["X-CERTEUS-PCO-fin.simulation"] = _json.dumps(
            pco["fin.alpha.simulation"], separators=(",", ":")
        )
    except Exception:
        pass
    try:
        from monitoring.metrics_slo import certeus_fin_commutator_rs

        # sygnał żywych metryk — używamy commutator jako placeholder
        certeus_fin_commutator_rs.set(1.0)
    except Exception:
        pass

    out = SimulateResponse(
        strategy_id=strat,
        capital_start=round(cap0, 2),
        capital_end=round(capT, 2),
        pnl_abs=round(pnl_abs, 2),
        pnl_pct=round(pnl_pct, 6),
        sharpe_stub=round(sharpe, 3),
        pco=pco,
    )

    # Zapamiętaj per-tenant (ostatnie 5 uruchomień)
    try:
        tenant = get_tenant_id(request)
        runs = _FIN_RUNS.setdefault(tenant, [])
        runs.append(out)
        if len(runs) > 5:
            del runs[:-5]
    except Exception:
        pass

    return out


@router.get("/pnl", response_model=PnLResponse)
async def pnl(request: Request) -> PnLResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=1)
    tenant = get_tenant_id(request)
    runs = list(_FIN_RUNS.get(tenant, []))
    return PnLResponse(tenant=tenant, runs=runs)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
