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


# Paper trading sandbox (per-tenant, prosta księga). W5 pilot.
class _PaperState(BaseModel):
    account_id: str = "default"
    cash: float = 10000.0
    position_qty: float = 0.0
    last_price: float = 0.0
    equity_curve: list[tuple[float, float]] = []  # (ts_epoch, equity)


_FIN_PAPER: dict[str, _PaperState] = {}


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

    # Build PCO (+ basic DPCO/MCO fields, W12) + W11 risk policy check
    policy: dict[str, object] = {
        "policy_ok": True,
        "violations": [],
        "thresholds": {"risk_max": 0.9, "sentiment_min": -1.0},
    }
    if risk > 0.9:
        policy["policy_ok"] = False
        policy.setdefault("violations", []).append("risk_above_max")  # type: ignore[arg-type]
    pco = {
        "fin.alpha.measure": {
            "signals": s,
            "operators": {"R": risk, "S": sent, "commutator_RS": comm_norm},
            "outcome": outcome,
            "p": round(p, 6),
            "policy": policy,
            # W12: Data governance fields (minimal)
            "dp_epsilon": 0.5,
            "consent_ref": "consent://demo",
            "lineage": ["io.email.mail_id", "cfe.geodesic_action"],
        }
    }

    # Feed LexQFT Path-Coverage with FIN signal (γ from p, uncaptured from 1-p)
    try:
        # Simple mapping: gamma in ~[0.85, 0.95], uncaptured small when confident
        gamma = max(0.0, min(0.99, 0.85 + 0.1 * p))
        unc = max(0.0, min(0.5, 0.2 * (1.0 - p)))
        from services.api_gateway.routers.lexqft import append_coverage_contribution

        append_coverage_contribution(gamma=gamma, weight=1.0, uncaptured=unc)
    except Exception:
        pass

    # Emit PCO header + metrics + ledger hash
    try:
        import json as _json

        response.headers["X-CERTEUS-PCO-fin.measure"] = _json.dumps(pco["fin.alpha.measure"], separators=(",", ":"))
        response.headers["X-CERTEUS-Policy-FIN"] = _json.dumps(policy, separators=(",", ":"))
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


# --- W7: Operators R/S commutator ---------------------------------------------


class OperatorsRSRequest(BaseModel):
    signals: dict[str, float] | None = None


class OperatorsRSResponse(BaseModel):
    R: float
    S: float
    commutator_norm: float


@router.post("/operators_rs", response_model=OperatorsRSResponse)
async def operators_rs(req: OperatorsRSRequest, request: Request, response: Response) -> OperatorsRSResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    s = req.signals or {}
    risk = float(sum(v for k, v in s.items() if "risk" in k.lower()))
    sent = float(sum(v for k, v in s.items() if ("sent" in k.lower()) or ("sentiment" in k.lower())))
    # Simple non‑commutation surrogate: absolute difference normalized
    denom = max(1.0, abs(risk) + abs(sent))
    comm = abs(risk - sent) / denom
    try:
        from monitoring.metrics_slo import certeus_fin_commutator_rs

        certeus_fin_commutator_rs.set(float(comm))
    except Exception:
        pass
    return OperatorsRSResponse(R=round(risk, 6), S=round(sent, 6), commutator_norm=round(comm, 6))


# --- W7: Entanglement MI (pairs) ---------------------------------------------


class MIItem(BaseModel):
    a: str
    b: str
    series_a: list[float]
    series_b: list[float]


class MISummary(BaseModel):
    pair: tuple[str, str]
    mi: float


class MIResponse(BaseModel):
    top: list[MISummary]


def _pearson_r(xs: list[float], ys: list[float]) -> float:
    try:
        n = min(len(xs), len(ys))
        if n == 0:
            return 0.0
        import math

        x = xs[:n]
        y = ys[:n]
        mx = sum(x) / n
        my = sum(y) / n
        vx = sum((u - mx) ** 2 for u in x)
        vy = sum((v - my) ** 2 for v in y)
        if vx <= 0 or vy <= 0:
            return 0.0
        cov = sum((u - mx) * (v - my) for (u, v) in zip(x, y, strict=False))
        r = cov / math.sqrt(vx * vy)
        return max(-1.0, min(1.0, r))
    except Exception:
        return 0.0


@router.post("/entanglement/mi", response_model=MIResponse)
async def entanglement_mi(items: list[MIItem], request: Request) -> MIResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=max(1, len(items)))
    out: list[MISummary] = []
    try:
        from monitoring.metrics_slo import certeus_fin_entanglement_mi
    except Exception:
        certeus_fin_entanglement_mi = None  # type: ignore
    for it in items:
        r = _pearson_r(it.series_a, it.series_b)
        # Gaussian assumption MI ~ -0.5 * ln(1 - r^2)
        import math

        try:
            mi = -0.5 * math.log(max(1e-9, 1.0 - (r * r)))
        except Exception:
            mi = 0.0
        mi = float(round(mi, 6))
        out.append(MISummary(pair=(it.a, it.b), mi=mi))
        try:
            if certeus_fin_entanglement_mi is not None:
                certeus_fin_entanglement_mi.labels(a=it.a, b=it.b).set(mi)
        except Exception:
            pass
    out.sort(key=lambda s: s.mi, reverse=True)
    return MIResponse(top=out[:5])


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


# --- W5: Paper trading sandbox ------------------------------------------------


class PaperOpenRequest(BaseModel):
    capital: float = 10_000.0
    account_id: str | None = None


class PaperOpenResponse(BaseModel):
    ok: bool
    account_id: str
    capital_start: float


class PaperOrderRequest(BaseModel):
    account_id: str | None = None
    side: str  # BUY or SELL
    qty: float
    price: float
    symbol: str | None = None


class PaperOrderResponse(BaseModel):
    ok: bool
    account_id: str
    position: float
    cash: float
    last_price: float
    equity: float
    pco: dict | None = None


class PaperPositionsResponse(BaseModel):
    account_id: str
    position: float
    cash: float
    last_price: float
    equity: float


class PaperEquityResponse(BaseModel):
    account_id: str
    series: list[tuple[float, float]]


def _get_paper(tenant: str) -> _PaperState:
    s = _FIN_PAPER.get(tenant)
    if s is None:
        s = _PaperState()
        _FIN_PAPER[tenant] = s
    return s


@router.post("/paper/open", response_model=PaperOpenResponse)
async def paper_open(req: PaperOpenRequest, request: Request) -> PaperOpenResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=1)
    tenant = get_tenant_id(request)
    st = _get_paper(tenant)
    st.cash = float(req.capital)
    st.position_qty = 0.0
    st.last_price = 0.0
    st.account_id = req.account_id or "default"
    st.equity_curve = []
    return PaperOpenResponse(ok=True, account_id=st.account_id, capital_start=st.cash)


@router.post("/paper/order", response_model=PaperOrderResponse)
async def paper_order(req: PaperOrderRequest, request: Request, response: Response) -> PaperOrderResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=1)
    tenant = get_tenant_id(request)
    st = _get_paper(tenant)
    side = (req.side or "").upper()
    qty = float(req.qty)
    px = float(req.price)
    if side not in {"BUY", "SELL"}:
        side = "BUY"
    if qty <= 0 or px <= 0:
        qty = max(0.0, qty)
        px = max(0.0, px)

    # Aktualizacja stanu konta (bez prowizji/slippage — W5 pilot)
    notional = qty * px
    if side == "BUY":
        st.cash -= notional
        st.position_qty += qty
    else:  # SELL
        st.cash += notional
        st.position_qty -= qty
    st.last_price = px

    # Equity i seria
    equity = st.cash + st.position_qty * st.last_price
    try:
        import time

        st.equity_curve.append((time.time(), float(equity)))
    except Exception:
        pass

    # Metryki + PCO
    try:
        from monitoring.metrics_slo import certeus_fin_paper_equity, certeus_fin_paper_orders_total

        certeus_fin_paper_orders_total.labels(tenant=tenant, side=side).inc()
        certeus_fin_paper_equity.labels(tenant=tenant).set(float(equity))
    except Exception:
        pass
    pco = {
        "fin.alpha.paper.order": {
            "tenant": tenant,
            "account": st.account_id,
            "side": side,
            "qty": qty,
            "price": px,
            "position": round(st.position_qty, 6),
            "cash": round(st.cash, 2),
            "equity": round(equity, 2),
        }
    }
    try:
        import json as _json

        response.headers["X-CERTEUS-PCO-fin.paper.order"] = _json.dumps(
            pco["fin.alpha.paper.order"], separators=(",", ":")
        )
    except Exception:
        pass
    return PaperOrderResponse(
        ok=True,
        account_id=st.account_id,
        position=round(st.position_qty, 6),
        cash=round(st.cash, 2),
        last_price=round(st.last_price, 6),
        equity=round(equity, 2),
        pco=pco,
    )


@router.get("/paper/positions", response_model=PaperPositionsResponse)
async def paper_positions(request: Request) -> PaperPositionsResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=1)
    tenant = get_tenant_id(request)
    st = _get_paper(tenant)
    eq = st.cash + st.position_qty * st.last_price
    return PaperPositionsResponse(
        account_id=st.account_id,
        position=round(st.position_qty, 6),
        cash=round(st.cash, 2),
        last_price=round(st.last_price, 6),
        equity=round(eq, 2),
    )


@router.get("/paper/equity", response_model=PaperEquityResponse)
async def paper_equity(request: Request) -> PaperEquityResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=1)
    tenant = get_tenant_id(request)
    st = _get_paper(tenant)
    return PaperEquityResponse(account_id=st.account_id, series=st.equity_curve)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
