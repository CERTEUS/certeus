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

from typing import Any

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel, Field

from monitoring.metrics_slo import (
    certeus_idem_new_total,
    certeus_idem_reused_total,
)
from security.ra import ra_fingerprint, tee_enabled
from services.api_gateway import idempotency as idem

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


class EntangleResponse(BaseModel):
    certificate: str

    achieved_negativity: float


class ChronoSyncRequest(BaseModel):
    coords: dict[str, Any]

    pc_delta: dict[str, Any] | None = None

    treaty_clause_skeleton: dict[str, Any] | None = None


class ChronoSyncResponse(BaseModel):
    reconciled: bool

    sketch: dict[str, Any]


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/devices.py                       |

# | ROLE: Devices stubs: HDE, Q-Oracle, Entangler, Chronosync           |

# +=====================================================================+

router = APIRouter(prefix="/v1/devices", tags=["devices"])

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
        HDEPlanAlternative(strategy="aggressive", cost_tokens=cost_aggr, expected_kappa=min(0.05, kappa * 1.1)),
    ]
    # W4: decyzja strategii zależna od celu horyzontu — dla wyższych progów
    # wybieramy wariant „aggressive”, inaczej „balanced” (deterministycznie).
    best = "aggressive" if target >= 0.28 else "balanced"
    result = HDEPlanResponse(
        evidence_plan=plan_balanced,
        plan_of_evidence=plan_balanced,
        cost_tokens=cost_bal,
        expected_kappa=kappa,
        alternatives=alt,
        best_strategy=best,
    )
    # W9: podpis urządzenia (opcjonalny; wymaga klucza ED25519 w ENV)
    try:
        import json as _json

        from monitoring.metrics_slo import certeus_devices_signed_total
        from security.signing import sign_payload

        sig = sign_payload(result.model_dump())
        certeus_devices_signed_total.labels(device="hde").inc()
        response.headers["X-CERTEUS-SIG-device"] = _json.dumps(sig, separators=(",", ":"))
    except Exception:
        pass
    # W10: TEE RA header (optional)
    try:
        if tee_enabled():
            from monitoring.metrics_slo import certeus_tee_ra_attested_total

            response.headers["X-CERTEUS-TEE-RA"] = _json.dumps(ra_fingerprint(), separators=(",", ":"))
            certeus_tee_ra_attested_total.labels(device="hde").inc()
    except Exception:
        pass
    try:
        idem.put(idem_key, result.model_dump())
        response.headers["X-Idempotency-Status"] = "new"
        certeus_idem_new_total.labels(endpoint="devices.hde.plan").inc()
    except Exception:
        pass
    return result


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

    text = (req.question or req.objective or "").strip()
    L = max(1, len(text))
    pA_base = min(0.8, 0.4 + (L % 10) * 0.02)
    # W2: lekka korekta pod constraints (jeśli podane), deterministyczna i ograniczona
    bias = 0.0
    try:
        cons = dict(req.constraints or {})
        cons_l = {str(k).lower(): v for k, v in cons.items()}
        if "maximize" in cons_l or "fairness" in cons_l or ("maximize fairness" in text.lower()):
            bias += 0.03
        risk_v = cons_l.get("risk")
        if isinstance(risk_v, int | float) and float(risk_v) > 0.5:
            bias -= 0.03
    except Exception:
        bias = 0.0
    pA = max(0.1, min(0.9, pA_base + bias))
    pB = max(0.1, 1.0 - pA)
    dist = [{"outcome": "A", "p": round(pA, 3)}, {"outcome": "B", "p": round(pB, 3)}]
    choice = "A" if pA >= pB else "B"
    result = QOracleResponse(
        optimum={"choice": choice, "reason": text or "heuristic"},
        payoff=round(max(pA, pB), 3),
        distribution=dist,
    )
    # W9: podpis i nagłówek
    try:
        import json as _json

        from monitoring.metrics_slo import certeus_devices_signed_total
        from security.signing import sign_payload

        sig = sign_payload(result.model_dump())
        certeus_devices_signed_total.labels(device="qoracle").inc()
        response.headers["X-CERTEUS-SIG-device"] = _json.dumps(sig, separators=(",", ":"))
    except Exception:
        pass
    try:
        if tee_enabled():
            from monitoring.metrics_slo import certeus_tee_ra_attested_total

            response.headers["X-CERTEUS-TEE-RA"] = _json.dumps(ra_fingerprint(), separators=(",", ":"))
            certeus_tee_ra_attested_total.labels(device="qoracle").inc()
    except Exception:
        pass
    try:
        idem.put(idem_key, result.model_dump())
        response.headers["X-Idempotency-Status"] = "new"
        certeus_idem_new_total.labels(endpoint="devices.qoracle.expectation").inc()
    except Exception:
        pass
    return result


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

    cert = "stub-certificate"
    try:
        response.headers["X-CERTEUS-PCO-entangler.certificate"] = cert
    except Exception:
        pass
    # W4: osiągana negatywność zależy łagodnie od liczby zmiennych (więcej → trudniej)
    nvars = max(1, len(req.variables))
    base = min(0.12, float(req.target_negativity))
    factor = max(0.5, 1.0 - 0.05 * max(0, nvars - 2))
    achieved = min(0.12, max(0.0, base * factor))
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
    out = EntangleResponse(certificate=cert, achieved_negativity=achieved)
    # W9: podpis + nagłówek
    try:
        import json as _json

        from monitoring.metrics_slo import certeus_devices_signed_total
        from security.signing import sign_payload

        sig = sign_payload(out.model_dump())
        certeus_devices_signed_total.labels(device="entangler").inc()
        response.headers["X-CERTEUS-SIG-device"] = _json.dumps(sig, separators=(",", ":"))
    except Exception:
        pass
    try:
        if tee_enabled():
            from monitoring.metrics_slo import certeus_tee_ra_attested_total

            response.headers["X-CERTEUS-TEE-RA"] = _json.dumps(ra_fingerprint(), separators=(",", ":"))
            certeus_tee_ra_attested_total.labels(device="entangler").inc()
    except Exception:
        pass
    try:
        idem.put(idem_key, out.model_dump())
        response.headers["X-Idempotency-Status"] = "new"
        certeus_idem_new_total.labels(endpoint="devices.entangle").inc()
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

    default_clauses = {
        "arbitration": "lex-domain mediator",
        "force_majeure": True,
        "revision_window_days": 14,
    }
    sketch = {
        "coords": req.coords,
        "pc_delta": req.pc_delta or {},
        "treaty": req.treaty_clause_skeleton or {"clauses": default_clauses},
    }

    out = ChronoSyncResponse(reconciled=True, sketch=sketch)
    # W9: podpis (bez nagłówka)
    try:
        from monitoring.metrics_slo import certeus_devices_signed_total
        from security.signing import sign_payload

        _ = sign_payload(out.model_dump())
        certeus_devices_signed_total.labels(device="chronosync").inc()
    except Exception:
        pass
    try:
        idem.put(idem_key, out.model_dump())
        response.headers["X-Idempotency-Status"] = "new"
        certeus_idem_new_total.labels(endpoint="devices.chronosync").inc()
    except Exception:
        pass
    return out


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
