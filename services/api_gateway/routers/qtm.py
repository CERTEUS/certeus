#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/qtm.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/qtm.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Stub API dla QTMP (pomiar). Zawiera wymagane pola: sequence[],

    uncertainty_bound.*, opcjonalnie decoherence i entanglement.

EN: QTMP (measurement) stub API. Includes required fields: sequence[],

    uncertainty_bound.*, optional decoherence and entanglement.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from hashlib import sha256
from pathlib import Path
from time import perf_counter
from typing import Any

from fastapi import APIRouter, HTTPException, Request, Response
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class InitCaseRequest(BaseModel):
    case: str | None = Field(default=None, description="Case identifier (optional)")
    state_uri: str | None = None

    basis: list[str] | None = Field(default=None, description="Measurement basis, e.g. ['ALLOW','DENY','ABSTAIN']")


class InitCaseResponse(BaseModel):
    ok: bool

    predistribution: list[dict[str, Any]]


class MeasureRequest(BaseModel):
    operator: str = Field(description="One of W/I/C/L/T (domain-dependent)")
    source: str | None = Field(default="ui", description="ui | chatops:<cmd> | mail:<id>")
    case: str | None = Field(default=None, description="Optional case identifier to bind decoherence/presets")
    basis: list[str] | None = None


class CollapseLog(BaseModel):
    sequence: list[dict[str, Any]]

    decoherence: dict[str, Any] | None = None


class MeasureResponse(BaseModel):
    verdict: str

    p: float

    collapse_log: CollapseLog

    uncertainty_bound: dict[str, float]

    latency_ms: float


class SequenceRequest(BaseModel):
    operators: list[str] = Field(..., min_items=1)
    case: str | None = Field(default=None)
    basis: list[str] | None = None


class SequenceStep(BaseModel):
    operator: str
    verdict: str
    p: float


class SequenceResponse(BaseModel):
    steps: list[SequenceStep]
    final_latency_ms: float
    uncertainty_bound: dict[str, float]


class CommutatorRequest(BaseModel):
    A: str

    B: str


class CommutatorResponse(BaseModel):
    value: float


class FindEntanglementRequest(BaseModel):
    variables: list[str]


class FindEntanglementResponse(BaseModel):
    pairs: list[tuple[str, str]]

    mi: float = 0.0

    negativity: float = 0.0


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/qtm.py                           |

# | ROLE: QTMP API stubs: init_case, measure, commutator, entanglement  |

# +=====================================================================+

router = APIRouter(prefix="/v1/qtm", tags=["QTMP"])

# Prosty graf spraw (case-graph) i rejestr kanałów dekoherencji (stub in-memory)
CASE_GRAPH: dict[str, dict[str, Any]] = {}
DECOHERENCE_REGISTRY: dict[str, dict[str, Any]] = {}
_PRESET_STORE_PATH = Path(__file__).resolve().parents[3] / "data" / "qtm_presets.json"


def _uniform_probs(basis: list[str]) -> list[float]:
    p = 1.0 / max(1, len(basis))
    return [round(p, 6) for _ in basis]


def _basis_probs_for_case(case_id: str, basis: list[str]) -> list[float]:
    cg = CASE_GRAPH.get(case_id)
    if cg and (pd := cg.get("predistribution")):
        mv = {str(x.get("state")): float(x.get("p", 0.0)) for x in pd}
        probs = [float(mv.get(b, 0.0)) for b in basis]
        s = sum(probs)
        if s > 0:
            probs = [round(x / s, 6) for x in probs]
            return probs
    return _uniform_probs(basis)


def _apply_decoherence(probs: list[float], case_id: str, basis: list[str]) -> list[float]:
    deco = DECOHERENCE_REGISTRY.get(case_id) or DECOHERENCE_REGISTRY.get("default")
    if not deco:
        return probs
    gamma = float(deco.get("gamma", 0.0) or 0.0)
    if gamma <= 0.0:
        return probs
    ch = str(deco.get("channel", "dephasing")).lower()
    n = len(probs)
    if ch in {"dephasing", "depolarizing"}:
        u = 1.0 / max(1, n)
        return [round((1.0 - gamma) * p + gamma * u, 6) for p in probs]
    if ch == "damping":
        # Move gamma mass to a selected state (e.g. DENY) deterministically
        try:
            idx_target = basis.index("DENY")
        except ValueError:
            idx_target = 0
        scaled = [(1.0 - gamma) * p for p in probs]
        scaled[idx_target] += gamma
        s = sum(scaled)
        return [round(p / s, 6) for p in scaled]
    # Fallback: uniform mix
    u = 1.0 / max(1, n)
    return [round((1.0 - gamma) * p + gamma * u, 6) for p in probs]


def _stable_index(key: str, mod: int) -> int:
    if mod <= 0:
        return 0
    h = int.from_bytes(sha256(key.encode("utf-8")).digest()[:4], "big")
    return h % mod


@router.post("/init_case", response_model=InitCaseResponse)
async def init_case(req: InitCaseRequest, request: Request) -> InitCaseResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    basis = req.basis or ["ALLOW", "DENY", "ABSTAIN"]

    # Simple uniform predistribution stub

    p = 1.0 / max(1, len(basis))

    predistribution = [{"state": b, "p": round(p, 6)} for b in basis]

    # Zapisz stan |Ψ⟩ w grafie spraw (stub)
    try:
        case_id = (req.case or "qtm-default").strip()
        CASE_GRAPH[case_id] = {
            "psi": req.state_uri or "psi://uniform",
            "basis": basis,
            "predistribution": predistribution,
        }
    except Exception:
        pass

    return InitCaseResponse(ok=True, predistribution=predistribution)


@router.post("/measure", response_model=MeasureResponse)
async def measure(req: MeasureRequest, request: Request, response: Response) -> MeasureResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    t0 = perf_counter()

    # Choose verdict based on operator hash; probabilities from case predistribution

    basis = req.basis or ["ALLOW", "DENY", "ABSTAIN"]

    # Resolve case id for decoherence/presets
    case_id = (req.case or req.source or "qtm-case").replace(":", "-")

    # Preset override: if preset stored for this case, use it
    try:
        _presets = _load_presets()
        op_effective = _presets.get(case_id, req.operator)
    except Exception:
        op_effective = req.operator

    idx = _stable_index(op_effective, len(basis))
    verdict = basis[idx]

    # Probability from predistribution (Born-like), smoothed by decoherence if configured
    probs0 = _basis_probs_for_case(case_id, basis)
    probs = _apply_decoherence(probs0, case_id, basis)
    p = float(probs[idx])

    sequence = [
        {
            "operator": op_effective,
            "timestamp": "now",
            "source": req.source or "ui",
        }
    ]

    # Decoherence: use registry if available for this case
    deco = DECOHERENCE_REGISTRY.get(case_id) or DECOHERENCE_REGISTRY.get("default") or {"channel": "dephasing"}
    collapse_log = CollapseLog(sequence=sequence, decoherence=deco)

    # Bridge CFE↔QTMP: use CFE curvature to influence uncertainty/priorities
    try:
        from services.api_gateway.routers.cfe import curvature as _cfe_curvature

        kappa = (await _cfe_curvature()).kappa_max  # type: ignore[misc]
    except Exception:
        kappa = 0.012

    # Simple correlation: higher curvature => slightly higher L_T bound
    ub = {"L_T": round(0.2 + min(0.2, kappa * 10.0), 3)}

    latency_ms = round((perf_counter() - t0) * 1000.0, 3)

    resp = MeasureResponse(verdict=verdict, p=p, collapse_log=collapse_log, uncertainty_bound=ub, latency_ms=latency_ms)

    # PCO headers: collapse event and optional predistribution from case-graph
    try:
        response.headers["X-CERTEUS-PCO-qtm.collapse_event"] = (
            f"{{\"operator\":\"{op_effective}\",\"verdict\":\"{verdict}\",\"channel\":\"{deco.get('channel', '')}\"}}"
        )
        cg = CASE_GRAPH.get(case_id)
        if cg and "predistribution" in cg:
            import json as _json

            response.headers["X-CERTEUS-PCO-qtm.predistribution[]"] = _json.dumps(
                cg["predistribution"], separators=(",", ":")
            )
        # Operator priorities influenced by curvature
        import json as _json

        base_pri = {"W": 1.0, "I": 1.0, "C": 1.0, "L": 1.0, "T": 1.0}
        boost = 1.0 + min(0.25, kappa * 10.0)
        base_pri["L"] = round(base_pri["L"] * boost, 3)
        base_pri["T"] = round(base_pri["T"] * boost, 3)
        response.headers["X-CERTEUS-PCO-qtmp.priorities"] = _json.dumps(base_pri, separators=(",", ":"))
        response.headers["X-CERTEUS-PCO-correlation.cfe_qtmp"] = str(round(kappa * 0.1, 6))
        response.headers["X-CERTEUS-PCO-qtm.collapse_prob"] = str(p)
        response.headers["X-CERTEUS-PCO-qtm.collapse_latency_ms"] = str(latency_ms)
    except Exception:
        pass

    # Append to in-memory history for this case
    try:
        hist = CASE_GRAPH.setdefault(case_id, {}).setdefault("history", [])
        hist.append(
            {"operator": op_effective, "verdict": verdict, "p": p, "ts": datetime.now(timezone.utc).isoformat()}
        )
    except Exception:
        pass

    # Export UB/priorities metrics to Prometheus + collapse counters and history length
    try:
        from monitoring.metrics_slo import (
            certeus_qtm_operator_priority,
            certeus_qtm_ub_lt,
            certeus_qtm_collapse_total,
            certeus_qtm_history_len,
        )

        certeus_qtm_ub_lt.labels(source=case_id).set(float(ub.get("L_T", 0.0)))
        for op_key, val in base_pri.items():
            certeus_qtm_operator_priority.labels(operator=op_key).set(float(val))
        certeus_qtm_collapse_total.labels(operator=op_effective, verdict=verdict).inc()
        try:
            _hist_len = len(CASE_GRAPH.get(case_id, {}).get("history", []))
            certeus_qtm_history_len.labels(case=case_id).set(_hist_len)
        except Exception:
            pass
    except Exception:
        pass

    # Record qtm.sequence into Ledger as provenance input (hash of sequence)
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        seq_hash = "sha256:" + compute_provenance_hash({"qtm.sequence": sequence}, include_timestamp=False)
        ledger_service.record_input(case_id=case_id, document_hash=seq_hash)
    except Exception:
        pass

    # Record collapse event into Ledger
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        collapse_event = {"qtm.collapse_event": {"operator": req.operator, "verdict": verdict, "decoherence": deco}}
        ev_hash = "sha256:" + compute_provenance_hash(collapse_event, include_timestamp=False)
        ledger_service.record_input(case_id=case_id, document_hash=ev_hash)
    except Exception:
        pass

    return resp


@router.post("/measure_sequence", response_model=SequenceResponse)
async def measure_sequence(req: SequenceRequest, request: Request, response: Response) -> SequenceResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=max(1, len(req.operators)))
    t0 = perf_counter()
    basis = req.basis or ["ALLOW", "DENY", "ABSTAIN"]
    case_id = (req.case or "qtm-seq").replace(":", "-")
    # Start with predistribution if present
    probs = _basis_probs_for_case(case_id, basis)
    steps: list[SequenceStep] = []
    for op in req.operators:
        idx = _stable_index(op, len(basis))
        verdict = basis[idx]
        probs = _apply_decoherence(probs, case_id, basis)
        p = float(probs[idx])
        steps.append(SequenceStep(operator=op, verdict=verdict, p=p))
        # Collapse to one-hot on verdict
        probs = [0.0 for _ in basis]
        probs[idx] = 1.0
    # UB as in measure()
    try:
        from services.api_gateway.routers.cfe import curvature as _cfe_curvature

        kappa = (await _cfe_curvature()).kappa_max  # type: ignore[misc]
    except Exception:
        kappa = 0.012
    ub = {"L_T": round(0.2 + min(0.2, kappa * 10.0), 3)}
    latency_ms = round((perf_counter() - t0) * 1000.0, 3)
    # Headers: record sequence PCO
    try:
        import json as _json

        response.headers["X-CERTEUS-PCO-qtm.sequence"] = _json.dumps(
            [s.model_dump() for s in steps], separators=(",", ":")
        )
    except Exception:
        pass
    # History append
    try:
        hist = CASE_GRAPH.setdefault(case_id, {}).setdefault("history", [])
        for s in steps:
            d = s.model_dump()
            d["ts"] = datetime.now(timezone.utc).isoformat()
            hist.append(d)
    except Exception:
        pass
    # Metrics
    try:
        from monitoring.metrics_slo import certeus_qtm_collapse_total, certeus_qtm_history_len

        hist_len = len(CASE_GRAPH.get(case_id, {}).get("history", []))
        certeus_qtm_history_len.labels(case=case_id).set(hist_len)
        for s in steps:
            certeus_qtm_collapse_total.labels(operator=s.operator, verdict=s.verdict).inc()
    except Exception:
        pass
    return SequenceResponse(steps=steps, final_latency_ms=latency_ms, uncertainty_bound=ub)


class QtmStateOut(BaseModel):
    case: str
    psi: str
    basis: list[str]
    predistribution: list[dict[str, Any]]


@router.get("/state/{case}", response_model=QtmStateOut)
async def get_state(case: str) -> QtmStateOut:
    cg = CASE_GRAPH.get(case)
    if not cg:
        raise HTTPException(status_code=404, detail="Case not found")
    return QtmStateOut(
        case=case,
        psi=str(cg.get("psi", "psi://unknown")),
        basis=list(cg.get("basis", [])),
        predistribution=list(cg.get("predistribution", [])),
    )


class QtmHistoryEvent(BaseModel):
    operator: str
    verdict: str
    p: float


class QtmHistoryOut(BaseModel):
    case: str
    history: list[QtmHistoryEvent]
    total: int
    offset: int
    limit: int


@router.get("/history/{case}", response_model=QtmHistoryOut)
async def get_history(case: str, offset: int = 0, limit: int = 100) -> QtmHistoryOut:
    cg = CASE_GRAPH.get(case)
    if not cg or "history" not in cg:
        raise HTTPException(status_code=404, detail="History not found")
    raw = cg.get("history", [])
    total = len(raw)
    start = max(0, int(offset))
    lmt = max(1, min(int(limit), 1000))
    sliced = raw[start : start + lmt]
    items = [QtmHistoryEvent(**e) for e in sliced]
    return QtmHistoryOut(case=case, history=items, total=total, offset=start, limit=lmt)


class OperatorsOut(BaseModel):
    operators: dict[str, dict[str, float]]


@router.get("/operators", response_model=OperatorsOut)
async def list_operators() -> OperatorsOut:
    # Example eigenvalue maps; can be made dynamic per domain
    return OperatorsOut(operators=_operator_eigs())


class UncertaintyOut(BaseModel):
    lower_bound: float


@router.get("/uncertainty", response_model=UncertaintyOut)
async def uncertainty_bound() -> UncertaintyOut:
    # Deterministic curvature-based bound to align with measure()
    try:
        from services.api_gateway.routers.cfe import curvature as _cfe_curvature

        kappa = (await _cfe_curvature()).kappa_max  # type: ignore[misc]
    except Exception:
        kappa = 0.012
    lb = round(0.2 + min(0.2, kappa * 10.0), 3)
    return UncertaintyOut(lower_bound=lb)


def _operator_eigs() -> dict[str, dict[str, float]]:
    return {
        "W": {"ALLOW": 1.0, "DENY": -1.0, "ABSTAIN": 0.0},
        "L": {"ALLOW": 0.9, "DENY": 0.1, "ABSTAIN": 0.5},
        "T": {"ALLOW": 0.2, "DENY": 0.8, "ABSTAIN": 0.6},
        "I": {"dolus directus": 1.0, "dolus eventualis": 0.5, "culpa": -0.2},
        "C": {"ALLOW": 0.0, "DENY": 1.0, "ABSTAIN": 0.5},
    }


class SetStateRequest(BaseModel):
    case: str = Field(..., min_length=1)
    psi: str | None = Field(default=None, description="State URI or descriptor")
    basis: list[str]
    probs: list[float] = Field(description="Probabilities aligned with basis; will be normalized")


@router.post("/state", response_model=QtmStateOut)
async def set_state(req: SetStateRequest) -> QtmStateOut:
    if len(req.basis) != len(req.probs):
        raise HTTPException(status_code=400, detail="basis/probs length mismatch")
    s = float(sum(req.probs))
    if s <= 0.0:
        raise HTTPException(status_code=400, detail="sum(probs) must be > 0")
    probs = [round(float(x) / s, 6) for x in req.probs]
    predistribution = [{"state": b, "p": p} for b, p in zip(req.basis, probs, strict=False)]
    CASE_GRAPH[req.case] = {
        "psi": req.psi or "psi://custom",
        "basis": list(req.basis),
        "predistribution": predistribution,
    }
    return QtmStateOut(
        case=req.case, psi=CASE_GRAPH[req.case]["psi"], basis=list(req.basis), predistribution=predistribution
    )


class ExpectationRequest(BaseModel):
    case: str
    operator: str


class ExpectationOut(BaseModel):
    value: float


@router.post("/expectation", response_model=ExpectationOut)
async def expectation(req: ExpectationRequest) -> ExpectationOut:
    cg = CASE_GRAPH.get(req.case)
    if not cg:
        raise HTTPException(status_code=404, detail="Case not found")
    basis: list[str] = list(cg.get("basis", [])) or ["ALLOW", "DENY", "ABSTAIN"]
    probs0 = [float(x.get("p", 0.0)) for x in cg.get("predistribution", [])]
    if len(probs0) != len(basis):
        probs0 = _uniform_probs(basis)
    # apply decoherence if configured
    probs = _apply_decoherence(probs0, req.case, basis)
    op_map = _operator_eigs().get(req.operator)
    if not op_map:
        raise HTTPException(status_code=400, detail="Unknown operator")
    # expectation: sum p_i * eig(state)
    val = 0.0
    for b, p in zip(basis, probs, strict=False):
        eig = float(op_map.get(b, 0.0))
        val += p * eig
    return ExpectationOut(value=round(val, 6))


class DeleteResult(BaseModel):
    ok: bool


@router.delete("/preset/{case}", response_model=DeleteResult)
async def delete_preset(case: str) -> DeleteResult:
    presets = _load_presets()
    if case not in presets:
        raise HTTPException(status_code=404, detail="Preset not found")
    presets.pop(case, None)
    _save_presets(presets)
    return DeleteResult(ok=True)


@router.delete("/state/{case}", response_model=DeleteResult)
async def delete_state(case: str) -> DeleteResult:
    if case not in CASE_GRAPH:
        raise HTTPException(status_code=404, detail="Case not found")
    CASE_GRAPH.pop(case, None)
    return DeleteResult(ok=True)


def _fractional_commutator(a: str, b: str) -> float:
    if a == b:
        return 0.0
    eigs = _operator_eigs()
    mA = eigs.get(a)
    mB = eigs.get(b)
    if not mA or not mB:
        return 1.0
    keys = set(mA.keys()) | set(mB.keys())
    num = 0.0
    den = 0.0
    for k in keys:
        vA = float(mA.get(k, 0.0))
        vB = float(mB.get(k, 0.0))
        num += abs(vA - vB)
        den += abs(vA) + abs(vB)
    if den <= 0.0:
        return 0.0
    return round(min(1.0, num / den), 3)


@router.post("/commutator", response_model=CommutatorResponse)
async def commutator(req: CommutatorRequest, request: Request) -> CommutatorResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    return CommutatorResponse(value=_fractional_commutator(req.A, req.B))


class DecoherenceRequest(BaseModel):
    case: str | None = Field(default=None, description="Case identifier or 'default'")
    channel: str = Field(description="dephasing | depolarizing | damping")
    gamma: float | None = Field(default=None, description="Channel parameter (optional)")


class DecoherenceResponse(BaseModel):
    ok: bool
    case: str
    channel: str
    gamma: float | None = None


@router.post("/decoherence", response_model=DecoherenceResponse)
async def set_decoherence(req: DecoherenceRequest, request: Request) -> DecoherenceResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    ch = req.channel.lower().strip()
    if ch not in {"dephasing", "depolarizing", "damping"}:
        ch = "dephasing"
    case_id = (req.case or "default").strip()
    cfg = {"channel": ch}
    if req.gamma is not None:
        cfg["gamma"] = float(req.gamma)
    DECOHERENCE_REGISTRY[case_id] = cfg
    return DecoherenceResponse(ok=True, case=case_id, channel=ch, gamma=req.gamma)


# === LOGIKA / LOGIC ===


def _load_presets() -> dict[str, str]:
    try:
        if _PRESET_STORE_PATH.exists():
            import json as _json

            return _json.loads(_PRESET_STORE_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return {}


def _save_presets(d: dict[str, str]) -> None:
    try:
        import json as _json

        _PRESET_STORE_PATH.parent.mkdir(parents=True, exist_ok=True)
        _PRESET_STORE_PATH.write_text(_json.dumps(d, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass


class PresetIn(BaseModel):
    case: str = Field(..., min_length=1)
    operator: str = Field(..., min_length=1, max_length=1)


class PresetOut(BaseModel):
    case: str
    operator: str


@router.post("/preset", response_model=PresetOut)
async def save_preset(p: PresetIn) -> PresetOut:
    presets = _load_presets()
    presets[p.case] = p.operator
    _save_presets(presets)
    return PresetOut(case=p.case, operator=p.operator)


@router.get("/preset/{case}", response_model=PresetOut)
async def get_preset(case: str) -> PresetOut:
    presets = _load_presets()
    op = presets.get(case)
    if not op:
        raise HTTPException(status_code=404, detail="Preset not found")
    return PresetOut(case=case, operator=op)


@router.get("/presets")
async def list_presets() -> list[PresetOut]:
    presets = _load_presets()
    return [PresetOut(case=k, operator=v) for k, v in presets.items()]


@router.post("/find_entanglement", response_model=FindEntanglementResponse)
async def find_entanglement(req: FindEntanglementRequest, request: Request) -> FindEntanglementResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    vars_ = req.variables[:]

    pairs: list[tuple[str, str]] = []

    # Pair consecutive variables as a stub

    for i in range(0, len(vars_) - 1, 2):
        pairs.append((vars_[i], vars_[i + 1]))

    # Provide low MI/negativity placeholders

    return FindEntanglementResponse(pairs=pairs, mi=0.05 if pairs else 0.0, negativity=0.03 if pairs else 0.0)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
class CommutatorExpRequest(BaseModel):
    case: str
    A: str
    B: str


@router.post("/commutator_expectation", response_model=CommutatorResponse)
async def commutator_expectation(req: CommutatorExpRequest, request: Request) -> CommutatorResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    cg = CASE_GRAPH.get(req.case)
    if not cg:
        raise HTTPException(status_code=404, detail="Case not found")
    basis: list[str] = list(cg.get("basis", [])) or ["ALLOW", "DENY", "ABSTAIN"]
    probs0 = [float(x.get("p", 0.0)) for x in cg.get("predistribution", [])]
    if len(probs0) != len(basis):
        probs0 = _uniform_probs(basis)
    probs = _apply_decoherence(probs0, req.case, basis)
    eigs = _operator_eigs()
    mA = eigs.get(req.A) or {}
    mB = eigs.get(req.B) or {}
    num = 0.0
    den = 0.0
    for b, p in zip(basis, probs, strict=False):
        vA = float(mA.get(b, 0.0))
        vB = float(mB.get(b, 0.0))
        num += p * abs(vA - vB)
        den += p * (abs(vA) + abs(vB))
    val = 0.0 if den <= 0 else min(1.0, num / den)
    return CommutatorResponse(value=round(val, 3))
