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

import json
from pathlib import Path

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class TunnelRequest(BaseModel):
    state_uri: str | None = None

    barrier_model: dict[str, float] | None = None

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

_COVERAGE_AGG: list[tuple[float, float, float]] = []  # (gamma, weight, uncaptured)
_COVERAGE_STORE = Path(__file__).resolve().parents[3] / "data" / "lexqft_coverage_state.json"

# Virtual pairs / energy debt state (per case)
_PAIRS_STORE = Path(__file__).resolve().parents[3] / "data" / "lexqft_pairs_state.json"
# case -> {"pairs": int, "energy_debt": float, "budget": float}
_PAIRS: dict[str, dict[str, float | int]] = {}
_RENORM_STORE = Path(__file__).resolve().parents[3] / "data" / "lexqft_renorm_state.json"
_RENORM: dict[str, dict[str, float]] = {}  # case -> {uid -> prob}


class CoverageResponse(BaseModel):
    coverage_gamma: float


@router.get("/coverage", response_model=CoverageResponse)
async def coverage() -> CoverageResponse:
    """PL/EN: Telemetria lexqft – gamma pokrycia (agregowana)."""
    global _COVERAGE_AGG
    # lazy-load persisted state if memory empty
    if not _COVERAGE_AGG and _COVERAGE_STORE.exists():
        try:
            raw = json.loads(_COVERAGE_STORE.read_text(encoding="utf-8"))
            _COVERAGE_AGG = [(float(x[0]), float(x[1]), float(x[2])) for x in raw]
        except Exception:
            _COVERAGE_AGG = []
    if _COVERAGE_AGG:
        tot_w = sum(w for _, w, _ in _COVERAGE_AGG) or 1.0
        gamma = sum(g * w for g, w, _ in _COVERAGE_AGG) / tot_w
        try:
            from monitoring.metrics_slo import certeus_lexqft_coverage_gamma

            certeus_lexqft_coverage_gamma.set(float(gamma))
        except Exception:
            pass
        return CoverageResponse(coverage_gamma=round(gamma, 6))
    return CoverageResponse(coverage_gamma=0.953)


@router.post("/tunnel", response_model=TunnelResponse)
async def tunnel(req: TunnelRequest, request: Request, response: Response) -> TunnelResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    # WKB-like approximation when barrier_model is present; otherwise fallback heuristic
    e = float(req.evidence_energy)
    V0: float | None = None
    w: float | None = None
    m: float | None = None
    bm = req.barrier_model if isinstance(req.barrier_model, dict) else None
    if bm is not None:
        try:
            V0 = float(bm.get("V0", bm.get("height", 0.8)))
            w = float(bm.get("w", bm.get("width", 1.0)))
            m = float(bm.get("m", bm.get("mass", 1.0)))
        except Exception:
            V0 = None
            w = None
            m = None

    if V0 is not None and w is not None and m is not None:
        # Clamp and compute
        import math as _math

        V0 = max(0.0, float(V0))
        w = max(0.0, float(w))
        m = max(1e-9, float(m))
        if e >= V0:
            p = 0.95
        else:
            kappa = _math.sqrt(max(V0 - e, 0.0) * m)
            p = _math.exp(-2.0 * w * kappa)
            p = max(0.0005, min(0.95, float(p)))
        min_e = float(V0)
    else:
        # Legacy heuristic: if energy > 1.0, tunneling is almost certain.
        p = 0.95 if e >= 1.0 else max(0.05, e * 0.6)
        min_e = 0.8

    path = ["start", "barrier", "post-barrier"] if p > 0.5 else ["start", "reflect"]
    resp = TunnelResponse(p_tunnel=round(float(p), 6), min_energy_to_cross=float(min_e), path=path)

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


# W3 — Virtual pairs & energy debt (budgeted)


class PairsBudgetIn(BaseModel):
    case: str
    budget: float = Field(ge=0)


class PairsSpawnIn(BaseModel):
    case: str
    pairs: int = Field(ge=1)
    energy_per_pair: float = Field(ge=0)


class PairsState(BaseModel):
    case: str
    pairs: int
    energy_debt: float
    budget: float
    remaining: float


def _pairs_load() -> None:
    global _PAIRS
    if _PAIRS:
        return
    try:
        if _PAIRS_STORE.exists():
            raw = json.loads(_PAIRS_STORE.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                _PAIRS = raw  # type: ignore[assignment]
    except Exception:
        _PAIRS = {}


def _pairs_save() -> None:
    try:
        _PAIRS_STORE.parent.mkdir(parents=True, exist_ok=True)
        _PAIRS_STORE.write_text(json.dumps(_PAIRS, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass


@router.post("/virtual_pairs/budget", response_model=PairsState)
async def pairs_set_budget(req: PairsBudgetIn, request: Request) -> PairsState:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    _pairs_load()
    st = _PAIRS.get(req.case) or {"pairs": 0, "energy_debt": 0.0, "budget": 0.0}
    st["budget"] = float(req.budget)
    _PAIRS[req.case] = st
    _pairs_save()
    remaining = float(st["budget"]) - float(st["energy_debt"])
    try:
        from monitoring.metrics_slo import certeus_lexqft_energy_debt

        certeus_lexqft_energy_debt.labels(case=req.case).set(float(st["energy_debt"]))
    except Exception:
        pass
    return PairsState(
        case=req.case,
        pairs=int(st["pairs"]),
        energy_debt=float(st["energy_debt"]),
        budget=float(st["budget"]),
        remaining=max(0.0, float(remaining)),
    )


@router.post("/virtual_pairs/spawn", response_model=PairsState)
async def pairs_spawn(req: PairsSpawnIn, request: Request, response: Response) -> PairsState:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)
    _pairs_load()
    st = _PAIRS.get(req.case) or {"pairs": 0, "energy_debt": 0.0, "budget": 100.0}
    want = int(req.pairs)
    cost = float(want) * float(req.energy_per_pair)
    new_debt = float(st["energy_debt"]) + cost
    budget = float(st.get("budget", 100.0))
    if new_debt > budget + 1e-9:
        # Over budget — refuse
        response.status_code = 409
    else:
        st["pairs"] = int(st.get("pairs", 0)) + want
        st["energy_debt"] = new_debt
        _PAIRS[req.case] = st
        _pairs_save()
    try:
        from monitoring.metrics_slo import certeus_lexqft_energy_debt

        certeus_lexqft_energy_debt.labels(case=req.case).set(float(st["energy_debt"]))
    except Exception:
        pass
    remaining = float(st.get("budget", 0.0)) - float(st["energy_debt"])
    return PairsState(
        case=req.case,
        pairs=int(st.get("pairs", 0)),
        energy_debt=float(st.get("energy_debt", 0.0)),
        budget=float(st.get("budget", 0.0)),
        remaining=max(0.0, float(remaining)),
    )


@router.get("/virtual_pairs/state", response_model=PairsState)
async def pairs_state(case: str) -> PairsState:
    _pairs_load()
    st = _PAIRS.get(case) or {"pairs": 0, "energy_debt": 0.0, "budget": 0.0}
    remaining = float(st.get("budget", 0.0)) - float(st.get("energy_debt", 0.0))
    try:
        from monitoring.metrics_slo import certeus_lexqft_energy_debt

        certeus_lexqft_energy_debt.labels(case=case).set(float(st.get("energy_debt", 0.0)))
    except Exception:
        pass
    return PairsState(
        case=case,
        pairs=int(st.get("pairs", 0)),
        energy_debt=float(st.get("energy_debt", 0.0)),
        budget=float(st.get("budget", 0.0)),
        remaining=max(0.0, float(remaining)),
    )


@router.post("/virtual_pairs/reset")
async def pairs_reset(case: str | None = None) -> dict:
    """Resetuje stan wirtualnych par (dla case lub globalnie)."""
    global _PAIRS
    _pairs_load()
    if case is None:
        _PAIRS = {}
    else:
        _PAIRS.pop(case, None)
    _pairs_save()
    return {"ok": True}


# Renormalizacja autorytetu (cldf.renorm.*)


class RenormItem(BaseModel):
    uid: str
    authority: float = Field(ge=0)
    weight: float = Field(default=1.0, ge=0)


class RenormRequest(BaseModel):
    case: str | None = None
    items: list[RenormItem]


class RenormOutItem(BaseModel):
    uid: str
    p: float


class RenormResponse(BaseModel):
    case: str
    dist: list[RenormOutItem]
    entropy: float


def _renorm_load() -> None:
    global _RENORM
    if _RENORM:
        return
    try:
        if _RENORM_STORE.exists():
            raw = json.loads(_RENORM_STORE.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                _RENORM = raw  # type: ignore[assignment]
    except Exception:
        _RENORM = {}


def _renorm_save() -> None:
    try:
        _RENORM_STORE.parent.mkdir(parents=True, exist_ok=True)
        _RENORM_STORE.write_text(json.dumps(_RENORM, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass


@router.post("/renorm", response_model=RenormResponse)
async def renorm(req: RenormRequest, response: Response) -> RenormResponse:
    """PL/EN: Renormalizacja autorytetu (CLDF) do rozkładu probabilistycznego.

    Zasady:
    - Ujemne i NaN traktowane jako 0.
    - Jeśli suma autorytetów==0 → rozkład jednostajny.
    - Wynik jest persistowany per-case.
    """

    _renorm_load()
    case = req.case or "lexqft-case"
    vals: list[tuple[str, float]] = []
    for it in req.items:
        try:
            a = float(it.authority) * max(0.0, float(it.weight))
        except Exception:
            a = 0.0
        if not (a >= 0.0):  # includes NaN
            a = 0.0
        vals.append((it.uid, a))
    s = sum(a for _, a in vals)
    if s <= 0.0:
        n = max(1, len(vals))
        dist = [(uid, 1.0 / n) for uid, _ in vals] if n else [("_", 1.0)]
    else:
        dist = [(uid, a / s) for uid, a in vals]

    # Persist
    _RENORM[case] = {uid: float(p) for uid, p in dist}
    _renorm_save()

    # Entropia Shannona (nats)
    import math as _m

    entropy = -sum(p * _m.log(p) for _, p in dist if p > 0.0)

    # PCO header: cldf.renorm.entropy
    try:
        response.headers["X-CERTEUS-PCO-cldf.renorm.entropy"] = str(entropy)
    except Exception:
        pass

    try:
        from monitoring.metrics_slo import certeus_lexqft_coverage_gamma as _noop  # keep import style consistent
        # (opcjonalnie można dodać dedykowany gauge, ale nie wymuszamy tutaj)
        _ = _noop
    except Exception:
        pass

    return RenormResponse(
        case=case,
        dist=[RenormOutItem(uid=uid, p=float(p)) for uid, p in dist],
        entropy=float(entropy),
    )


class CoverageItem(BaseModel):
    gamma: float
    weight: float = 1.0
    uncaptured: float = 0.0


@router.post("/coverage/update")
async def coverage_update(items: list[CoverageItem], request: Request) -> dict:
    """PL/EN: Ustaw (zastąp) wkłady ścieżek do pokrycia (gamma, wagi, uncaptured)."""
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    global _COVERAGE_AGG
    _COVERAGE_AGG = [(float(it.gamma), float(it.weight), float(it.uncaptured)) for it in items]
    # persist state
    try:
        _COVERAGE_STORE.parent.mkdir(parents=True, exist_ok=True)
        _COVERAGE_STORE.write_text(json.dumps(_COVERAGE_AGG), encoding="utf-8")
    except Exception:
        pass
    return {"ok": True, "count": len(_COVERAGE_AGG)}


@router.post("/coverage/reset")
async def coverage_reset(request: Request) -> dict:
    """PL/EN: Resetuje stan agregatora pokrycia do wartości domyślnych (empty)."""
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    global _COVERAGE_AGG
    _COVERAGE_AGG = []
    try:
        if _COVERAGE_STORE.exists():
            _COVERAGE_STORE.unlink()
    except Exception:
        pass
    return {"ok": True}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===


class CoverageState(BaseModel):
    coverage_gamma: float
    uncaptured_mass: float


@router.get("/coverage/state", response_model=CoverageState)
async def coverage_state() -> CoverageState:
    """PL/EN: Zwraca stan agregatora: gamma i łączną uncaptured_mass (ważoną)."""
    if _COVERAGE_AGG:
        tot_w = sum(w for _, w, _ in _COVERAGE_AGG) or 1.0
        gamma = sum(g * w for g, w, _ in _COVERAGE_AGG) / tot_w
        unc = sum(u * w for _, w, u in _COVERAGE_AGG) / tot_w
        from monitoring.metrics_slo import certeus_lexqft_coverage_gamma, certeus_lexqft_uncaptured_mass

        try:
            certeus_lexqft_coverage_gamma.set(float(gamma))
            certeus_lexqft_uncaptured_mass.set(float(unc))
        except Exception:
            pass

        return CoverageState(coverage_gamma=round(gamma, 6), uncaptured_mass=round(unc, 6))
    return CoverageState(coverage_gamma=0.953, uncaptured_mass=0.02)
