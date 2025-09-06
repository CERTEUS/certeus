#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/devices.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/devices.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla obszaru urządzenia HDE/Q-Oracle/Entangle/Chronosync.

EN: FastAPI router for HDE/Q-Oracle/Entangle/Chronosync devices.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import base64
import json as _json
import os
from time import time
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel, Field

from monitoring.metrics_slo import certeus_idem_reused_total
from services.api_gateway import idempotency as idem

# Optional metrics & attestation (import lazily where used to avoid unused warnings)

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class HDEPlanRequest(BaseModel):
    case: str | None = None

    target_horizon: float | None = Field(default=0.2, description="Desired horizon mass threshold")


class HDEPlanAlternative(BaseModel):
    strategy: str
    cost_tokens: int
    expected_kappa: float


class HDEPlanResponse(BaseModel):
    evidence_plan: list[dict[str, Any]]
    plan_of_evidence: list[dict[str, Any]]
    cost_tokens: int
    expected_kappa: float
    alternatives: list[HDEPlanAlternative] | None = None
    best_strategy: str | None = None


class QOracleRequest(BaseModel):
    objective: str | None = None
    question: str | None = None
    constraints: dict[str, Any] | None = None


class QOracleResponse(BaseModel):
    optimum: dict[str, Any]

    payoff: float

    distribution: list[dict[str, Any]]


class EntangleRequest(BaseModel):
    variables: list[str]

    target_negativity: float = 0.1

    scenario: str | None = Field(default=None, description="Scenario label (e.g., 'pairwise', 'global')")


class EntangleResponse(BaseModel):
    certificate: str

    achieved_negativity: float

    scenario: str | None = None

    pairs: list[dict[str, float]] | None = None


class ChronoSyncRequest(BaseModel):
    coords: dict[str, Any]

    pc_delta: dict[str, Any] | None = None

    treaty_clause_skeleton: dict[str, Any] | None = None

    protocol: str | None = Field(default=None, description="Protocol tag (e.g., 'mediation.v1')")


class ChronoSyncResponse(BaseModel):
    reconciled: bool

    sketch: dict[str, Any]

    protocol: str | None = None

    collisions_count: int | None = None

    mediated: bool | None = None


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/devices.py                       |

# | ROLE: Devices stubs: HDE, Q-Oracle, Entangler, Chronosync           |

# +=====================================================================+

router = APIRouter(prefix="/v1/devices", tags=["devices"])

# Prosty store idempotency (in-proc). Klucz: path + Idempotency-Key
_IDEMP_TTL_SEC = 300.0
_IDEMP_STORE: dict[str, tuple[float, dict[str, Any]]] = {}


def _get_idemp_key(request: Request) -> str | None:
    key = request.headers.get("X-Idempotency-Key") or request.headers.get("Idempotency-Key")
    key = (key or "").strip()
    return key or None


def _ttl() -> float:
    try:
        v = float(os.getenv("IDEMP_TTL_SEC") or _IDEMP_TTL_SEC)
        return max(0.0, v)
    except Exception:
        return _IDEMP_TTL_SEC


def _cache_get(path: str, key: str) -> dict[str, Any] | None:
    try:
        k = f"{path}::{key}"
        item = _IDEMP_STORE.get(k)
        if not item:
            return None
        exp, payload = item
        # Expired when expiration time is at or before now (TTL==0 expires immediately)
        if exp <= time():
            # expired
            try:
                _IDEMP_STORE.pop(k, None)
            except Exception:
                pass
            return None
        return payload
    except Exception:
        return None


def _cache_set(path: str, key: str, payload: dict[str, Any]) -> None:
    try:
        _IDEMP_STORE[f"{path}::{key}"] = (time() + _ttl(), dict(payload))
    except Exception:
        pass


# Horizon Drive Engine (HDE)


@router.post("/horizon_drive/plan", response_model=HDEPlanResponse)
async def hde_plan(_req: HDEPlanRequest, request: Request, response: Response) -> HDEPlanResponse:
    from services.api_gateway.limits import enforce_limits

    idem_key = request.headers.get("Idempotency-Key")
    cached = idem.get(idem_key)
    if cached is not None:
        try:
            response.headers["X-Idempotency-Status"] = "reused"
        except Exception:
            pass
        certeus_idem_reused_total.labels(endpoint="devices.hde.plan").inc()
        return HDEPlanResponse(**cached)

    enforce_limits(request, cost_units=2)

    # Idempotency check
    _k = _get_idemp_key(request)
    path_key = "/v1/devices/horizon_drive/plan"
    if _k:
        cached = _cache_get(path_key, _k)
        if cached is not None:
            try:
                response.headers["X-Idempotent-Replay"] = "1"
                try:
                    from monitoring.metrics_slo import certeus_idempotent_replay_total

                    certeus_idempotent_replay_total.labels(path=path_key, hit="1").inc()
                except Exception:
                    pass
            except Exception:
                pass
            return HDEPlanResponse(**cached)

    plan_balanced = [
        {"action": "collect_email_evidence", "weight": 0.4},
        {"action": "request_affidavit", "weight": 0.6},
    ]
    # aggressive plan variant (kept for comparison in alternatives)
    _plan_aggr = [
        {"action": "collect_email_evidence", "weight": 0.3},
        {"action": "request_affidavit", "weight": 0.4},
        {"action": "expert_opinion", "weight": 0.3},
    ]
    target = float(_req.target_horizon or 0.2)
    try:
        from services.api_gateway.routers.cfe import curvature as _cfe_curvature

        kappa = (await _cfe_curvature()).kappa_max  # type: ignore[misc]
    except Exception:
        kappa = 0.012
    cost_bal = max(30, int(200 * target))
    cost_aggr = max(40, int(280 * target))
    alt: list[HDEPlanAlternative] = [
        HDEPlanAlternative(strategy="balanced", cost_tokens=cost_bal, expected_kappa=kappa),
        HDEPlanAlternative(
            strategy="aggressive",
            cost_tokens=cost_aggr,
            expected_kappa=min(0.05, kappa * 1.1),
        ),
    ]
    # Comparative planner: balance cost vs. reaching target horizon mass (proxy via expected_kappa)
    max_cost = max(a.cost_tokens for a in alt) or 1

    def _estimate_horizon_from_kappa(k: float) -> float:
        return max(0.0, min(1.0, k * 4.0))

    weight_target = 0.3 if target <= 0.25 else 0.6

    def _score(a: HDEPlanAlternative) -> float:
        cost_norm = a.cost_tokens / max_cost
        horizon = _estimate_horizon_from_kappa(a.expected_kappa)
        shortfall = max(0.0, float(target) - horizon)
        return (1.0 - weight_target) * cost_norm + weight_target * shortfall

    best = min(alt, key=_score).strategy
    out = HDEPlanResponse(
        evidence_plan=plan_balanced,
        plan_of_evidence=plan_balanced,
        cost_tokens=cost_bal,
        expected_kappa=kappa,
        alternatives=alt,
        best_strategy=best,
    )
    if _k:
        _cache_set(path_key, _k, out.model_dump())
        try:
            response.headers["X-Idempotent-Replay"] = "0"
            try:
                from monitoring.metrics_slo import certeus_idempotent_replay_total

                certeus_idempotent_replay_total.labels(path=path_key, hit="0").inc()
            except Exception:
                pass
        except Exception:
            pass
    # Signing header (Ed25519) over canonical JSON of body
    try:
        pem = os.getenv("ED25519_PRIVKEY_PEM") or ""
        if pem.strip():
            sk = serialization.load_pem_private_key(pem.encode("utf-8"), password=None)
            assert isinstance(sk, Ed25519PrivateKey)
            body = out.model_dump()
            canon = _json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
            sig = sk.sign(canon)
            sig_b64u = base64.urlsafe_b64encode(sig).rstrip(b"=").decode("ascii")
            meta = {"alg": "EdDSA", "sig": sig_b64u}
            response.headers["X-CERTEUS-SIG-device"] = _json.dumps(meta)
    except Exception:
        pass
    # TEE RA header (optional, when enabled)
    try:
        if (os.getenv("TEE_ENABLED") or "").strip() in {"1", "true", "True"}:
            fp = os.getenv("ED25519_PUBKEY_HEX", "")[:16] or "tee-dev"
            response.headers["X-CERTEUS-TEE-RA"] = _json.dumps({"fingerprint": fp})
    except Exception:
        pass
    return out


# Quantum Oracle (QOC)


@router.post("/qoracle/expectation", response_model=QOracleResponse)
async def qoracle_expectation(req: QOracleRequest, request: Request, response: Response) -> QOracleResponse:
    from services.api_gateway.limits import enforce_limits

    idem_key = request.headers.get("Idempotency-Key")
    cached = idem.get(idem_key)
    if cached is not None:
        try:
            response.headers["X-Idempotency-Status"] = "reused"
        except Exception:
            pass
        certeus_idem_reused_total.labels(endpoint="devices.qoracle.expectation").inc()
        return QOracleResponse(**cached)

    enforce_limits(request, cost_units=2)

    # Idempotency check
    _k = _get_idemp_key(request)
    path_key = "/v1/devices/qoracle/expectation"
    if _k:
        cached = _cache_get(path_key, _k)
        if cached is not None:
            try:
                response.headers["X-Idempotent-Replay"] = "1"
                try:
                    from monitoring.metrics_slo import certeus_idempotent_replay_total

                    certeus_idempotent_replay_total.labels(path=path_key, hit="1").inc()
                except Exception:
                    pass
            except Exception:
                pass
            return QOracleResponse(**cached)

    text = (req.question or req.objective or "").strip()
    L = max(1, len(text))
    # Base heuristic from prompt length
    pA_base = 0.4 + (L % 10) * 0.02  # in [0.4, 0.58]

    # Lightweight adjustments from constraints and keywords
    kw_bonus = 0.0
    low = text.lower()
    if "maximize" in low:
        kw_bonus += 0.01
    if "minimize" in low:
        kw_bonus -= 0.01

    c_bonus = 0.0
    try:
        cons = req.constraints or {}
        numeric = [float(v) for v in cons.values() if isinstance(v, int | float)]
        if numeric:
            csum = sum(numeric)
            # Center around ~100 and scale gently; clamp to ±0.05
            c_bonus = max(-0.05, min(0.05, (csum - 100.0) / 1000.0))
    except Exception:
        c_bonus = 0.0

    pA = max(0.1, min(0.8, pA_base + kw_bonus + c_bonus))
    pB = max(0.1, 1.0 - pA)
    dist = [{"outcome": "A", "p": round(pA, 3)}, {"outcome": "B", "p": round(pB, 3)}]
    choice = "A" if pA >= pB else "B"
    out = QOracleResponse(
        optimum={"choice": choice, "reason": text or "heuristic"},
        payoff=round(max(pA, pB), 3),
        distribution=dist,
    )
    if _k:
        _cache_set(path_key, _k, out.model_dump())
        try:
            response.headers["X-Idempotent-Replay"] = "0"
            try:
                from monitoring.metrics_slo import certeus_idempotent_replay_total

                certeus_idempotent_replay_total.labels(path=path_key, hit="0").inc()
            except Exception:
                pass
        except Exception:
            pass
    # TEE RA header (optional)
    try:
        if (os.getenv("TEE_ENABLED") or "").strip() in {"1", "true", "True"}:
            fp = os.getenv("ED25519_PUBKEY_HEX", "")[:16] or "tee-dev"
            response.headers["X-CERTEUS-TEE-RA"] = _json.dumps({"fingerprint": fp})
    except Exception:
        pass
    return out


# Entanglement Inducer (EI)


@router.post("/entangle", response_model=EntangleResponse)
async def entangle(req: EntangleRequest, request: Request, response: Response) -> EntangleResponse:
    from services.api_gateway.limits import enforce_limits

    idem_key = request.headers.get("Idempotency-Key")
    cached = idem.get(idem_key)
    if cached is not None:
        try:
            response.headers["X-Idempotency-Status"] = "reused"
        except Exception:
            pass
        certeus_idem_reused_total.labels(endpoint="devices.entangle").inc()
        return EntangleResponse(**cached)

    enforce_limits(request, cost_units=2)

    # Idempotency check
    _k = _get_idemp_key(request)
    path_key = "/v1/devices/entangle"
    if _k:
        cached = _cache_get(path_key, _k)
        if cached is not None:
            try:
                response.headers["X-Idempotent-Replay"] = "1"
                try:
                    from monitoring.metrics_slo import certeus_idempotent_replay_total

                    certeus_idempotent_replay_total.labels(path=path_key, hit="1").inc()
                except Exception:
                    pass
            except Exception:
                pass
            return EntangleResponse(**cached)

    cert = "stub-certificate"
    try:
        response.headers["X-CERTEUS-PCO-entangler.certificate"] = cert
    except Exception:
        pass
    achieved = min(0.12, float(req.target_negativity))
    pairs: list[dict[str, float]] | None = None
    if len(req.variables) >= 2:
        pairs = []
        for i in range(len(req.variables) - 1):
            a, b = req.variables[i], req.variables[i + 1]
            pairs.append({f"{a}|{b}": round(achieved * 0.8, 6)})
    try:
        from monitoring.metrics_slo import Gauge

        global _devices_negativity  # type: ignore
        try:  # noqa: SIM105 (explicit check)
            _ = _devices_negativity  # type: ignore[name-defined,used-before-assignment]
        except NameError:  # define once lazily
            _devices_negativity = Gauge(
                "certeus_devices_negativity",
                "Devices entangler negativity",
                labelnames=("var",),
            )
        for v in req.variables:
            _devices_negativity.labels(var=v).set(achieved)
    except Exception:
        pass
    out = EntangleResponse(
        certificate=cert,
        achieved_negativity=achieved,
        scenario=req.scenario,
        pairs=pairs,
    )
    if _k:
        _cache_set(path_key, _k, out.model_dump())
        try:
            response.headers["X-Idempotent-Replay"] = "0"
            try:
                from monitoring.metrics_slo import certeus_idempotent_replay_total

                certeus_idempotent_replay_total.labels(path=path_key, hit="0").inc()
            except Exception:
                pass
        except Exception:
            pass
    return out


# Chronosync (LCSI)


@router.post("/chronosync/reconcile", response_model=ChronoSyncResponse)
async def chronosync_reconcile(req: ChronoSyncRequest, request: Request, response: Response) -> ChronoSyncResponse:
    from services.api_gateway.limits import enforce_limits

    idem_key = request.headers.get("Idempotency-Key")
    cached = idem.get(idem_key)
    if cached is not None:
        try:
            response.headers["X-Idempotency-Status"] = "reused"
        except Exception:
            pass
        certeus_idem_reused_total.labels(endpoint="devices.chronosync").inc()
        return ChronoSyncResponse(**cached)

    enforce_limits(request, cost_units=2)

    # Idempotency check
    _k = _get_idemp_key(request)
    path_key = "/v1/devices/chronosync/reconcile"
    if _k:
        cached = _cache_get(path_key, _k)
        if cached is not None:
            try:
                response.headers["X-Idempotent-Replay"] = "1"
                try:
                    from monitoring.metrics_slo import certeus_idempotent_replay_total

                    certeus_idempotent_replay_total.labels(path=path_key, hit="1").inc()
                except Exception:
                    pass
            except Exception:
                pass
            return ChronoSyncResponse(**cached)

    default_clauses = {
        "arbitration": "lex-domain mediator",
        "force_majeure": True,
        "revision_window_days": 14,
    }
    collisions = 0
    try:
        if isinstance(req.pc_delta, dict):
            collisions = len(req.pc_delta)
    except Exception:
        collisions = 0

    sketch = {
        "coords": req.coords,
        "pc_delta": req.pc_delta or {},
        "treaty": req.treaty_clause_skeleton or {"clauses": default_clauses},
    }
    out = ChronoSyncResponse(
        reconciled=True,
        sketch=sketch,
        protocol=req.protocol,
        collisions_count=collisions,
        mediated=collisions > 0,
    )
    if _k:
        _cache_set(path_key, _k, out.model_dump())
        try:
            response.headers["X-Idempotent-Replay"] = "0"
            try:
                from monitoring.metrics_slo import certeus_idempotent_replay_total

                certeus_idempotent_replay_total.labels(path=path_key, hit="0").inc()
            except Exception:
                pass
        except Exception:
            pass
    return out


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
