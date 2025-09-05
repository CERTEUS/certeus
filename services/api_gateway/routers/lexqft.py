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

    barrier_model: dict | None = None

    evidence_energy: float = Field(ge=0)

    counter_arguments: list[str] | None = None


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
_TUNNEL_LOG = Path(__file__).resolve().parents[3] / "data" / "lexqft_tunnel_log.jsonl"


def _persist_coverage_state() -> None:
    try:
        _COVERAGE_STORE.parent.mkdir(parents=True, exist_ok=True)
        _COVERAGE_STORE.write_text(json.dumps(_COVERAGE_AGG), encoding="utf-8")
    except Exception:
        pass


def append_coverage_contribution(gamma: float, weight: float = 1.0, uncaptured: float = 0.0) -> None:
    """PL/EN: Dodaj wkład do agregatora pokrycia i zapisz stan (bez FastAPI request).

    Safe to import and call from other routers (e.g., FIN) to feed coverage.
    """
    global _COVERAGE_AGG
    _COVERAGE_AGG.append((float(gamma), float(weight), float(uncaptured)))
    _persist_coverage_state()


class BarrierScenario(BaseModel):
    model_id: str
    energy: float
    model_uri: str


@router.get("/tunnel/scenarios", response_model=list[BarrierScenario])
async def tunnel_scenarios() -> list[BarrierScenario]:
    """PL/EN: Przykładowe modele bariery, do szybkich testów scenariuszy.

    Nie jest to kontrakt fizyczny — jedynie katalog demonstracyjny modeli.
    """
    return [
        BarrierScenario(model_id="thin", energy=0.8, model_uri="lexqft://barrier/thin"),
        BarrierScenario(model_id="thick", energy=1.5, model_uri="lexqft://barrier/thick"),
        BarrierScenario(model_id="stepped", energy=1.2, model_uri="lexqft://barrier/stepped"),
    ]


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

    # Placeholder physics:
    # - If a barrier model is provided, use its energy as the threshold.
    # - Otherwise keep the legacy rule (>=1.0 almost certain).

    e = req.evidence_energy
    min_e = 0.8
    if isinstance(req.barrier_model, dict) and req.barrier_model:
        try:
            be = req.barrier_model.get("energy") or req.barrier_model.get("barrier_energy")
            if be is not None:
                min_e = float(be)
        except Exception:
            pass
        # Probability scales with ratio e/min_e until cap; 0.6 factor keeps
        # continuity with previous heuristic.
        if e >= float(min_e):
            p = 0.95
        else:
            denom = float(min_e) if float(min_e) > 1e-9 else 1.0
            p = max(0.05, (e / denom) * 0.6)
    else:
        p = 0.95 if e >= 1.0 else max(0.05, e * 0.6)

    path = ["start", "barrier", "post-barrier"] if p > 0.5 else ["start", "reflect"]
    resp = TunnelResponse(p_tunnel=round(p, 6), min_energy_to_cross=min_e, path=path)

    # PCO headers: qlaw.tunneling.*
    try:
        response.headers["X-CERTEUS-PCO-qlaw.tunneling.p"] = str(resp.p_tunnel)
        response.headers["X-CERTEUS-PCO-qlaw.tunneling.path"] = "/".join(path)
        response.headers["X-CERTEUS-PCO-qlaw.tunneling.min_energy"] = str(min_e)
        try:
            # Optional model URI passthrough
            model_uri = None
            if isinstance(req.barrier_model, dict):
                model_uri = req.barrier_model.get("model_uri") or req.barrier_model.get("uri")
            if model_uri:
                response.headers["X-CERTEUS-PCO-qlaw.tunneling.model_uri"] = str(model_uri)
        except Exception:
            pass
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

    # Append lightweight log entry (kontr-dowody, model, wynik)
    try:
        from datetime import datetime
        import json as _json

        entry = {
            "ts": datetime.utcnow().isoformat() + "Z",
            "case_id": req.state_uri or "lexqft-case",
            "barrier_energy": float(min_e),
            "p_tunnel": float(resp.p_tunnel),
            "path": path,
            "counter_arguments": req.counter_arguments or [],
        }
        _TUNNEL_LOG.parent.mkdir(parents=True, exist_ok=True)
        with _TUNNEL_LOG.open("a", encoding="utf-8") as fh:
            fh.write(_json.dumps(entry, ensure_ascii=False) + "\n")
        try:
            from monitoring.metrics_slo import certeus_lexqft_tunnel_events_total

            certeus_lexqft_tunnel_events_total.inc()
        except Exception:
            pass
    except Exception:
        pass

    return resp


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


class CoverageContribution(BaseModel):
    gamma: float
    weight: float
    uncaptured: float


@router.get("/coverage/contributions", response_model=list[CoverageContribution])
async def coverage_contributions() -> list[CoverageContribution]:
    """PL/EN: Surowa lista wkładów do pokrycia (gamma, weight, uncaptured)."""
    out: list[CoverageContribution] = []
    for g, w, u in _COVERAGE_AGG:
        out.append(CoverageContribution(gamma=float(g), weight=float(w), uncaptured=float(u)))
    return out


class TunnelStats(BaseModel):
    count: int
    last_ts: str | None = None


@router.get("/tunnel/stats", response_model=TunnelStats)
async def tunnel_stats() -> TunnelStats:
    """PL/EN: Statystyki tunelowania: liczba wpisów i ostatni timestamp.

    Bazuje na lekkim logu JSONL w `data/lexqft_tunnel_log.jsonl`.
    """
    try:
        if not _TUNNEL_LOG.exists():
            return TunnelStats(count=0, last_ts=None)
        # Count lines and parse last non-empty
        last_ts: str | None = None
        count = 0
        with _TUNNEL_LOG.open("r", encoding="utf-8") as fh:
            for ln in fh:
                s = ln.strip()
                if not s:
                    continue
                count += 1
                last_ts = None  # will set below
            # Re-read last line efficiently
        # Fallback simple read for last line
        try:
            data = _TUNNEL_LOG.read_text(encoding="utf-8").strip().splitlines()
            if data:
                import json as _json

                obj = _json.loads(data[-1])
                last_ts = str(obj.get("ts"))
        except Exception:
            pass
        return TunnelStats(count=int(count), last_ts=last_ts)
    except Exception:
        return TunnelStats(count=0, last_ts=None)
