# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/proofgate/app.py                           |

# | ROLE: Project module.                                       |

# | PLIK: services/proofgate/app.py                           |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Mapping
import os
from pathlib import Path
from typing import Any

from fastapi import FastAPI
from fastapi.openapi.utils import get_openapi
from pydantic import BaseModel, Field
import yaml

from core.version import __version__
from monitoring.metrics_slo import observe_decision
from monitoring.otel_setup import set_span_attrs, setup_fastapi_otel
from services.ledger_service.ledger import (
    compute_provenance_hash,
    ledger_service,
)

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class PublishRequest(BaseModel):
    pco: dict[str, Any] | None = Field(default=None, description="Proof-Carrying Object")

    policy: dict[str, Any] | None = None

    budget_tokens: int | None = None


class PublishResponse(BaseModel):
    status: str

    pco: dict[str, Any] | None = None

    ledger_ref: str | None = None


# === LOGIKA / LOGIC ===

app = FastAPI(title="ProofGate", version=__version__)
setup_fastapi_otel(app)


@app.get("/healthz")
def healthz() -> dict[str, Any]:
    return {"ok": True, "service": "proofgate-stub"}


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def _load_policy_pack() -> dict[str, Any]:
    p = _repo_root() / "policies" / "pco" / "policy_pack.yaml"

    try:
        return yaml.safe_load(p.read_text(encoding="utf-8")) or {}

    except Exception:
        return {}


def _load_governance_pack() -> dict[str, Any]:
    try:
        p = _repo_root() / "policies" / "governance" / "governance_pack.v0.1.yaml"
        return yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    except Exception:
        return {}


def _infer_domain(pco: Mapping[str, Any]) -> str:
    # Explicit field
    d = pco.get("domain") if isinstance(pco, Mapping) else None
    if isinstance(d, str) and d:
        return d.lower().strip()
    # Case prefix heuristic
    case_id = str(pco.get("case_id") or pco.get("rid") or "")
    if case_id.startswith("CER-LEX"):
        return "lex"
    if case_id.startswith("CER-FIN"):
        return "fin"
    if case_id.startswith("CER-SEC"):
        return "sec"
    # Payload keys heuristic
    keys = set(pco.keys()) if isinstance(pco, Mapping) else set()
    if {"signals", "dp_epsilon"} & keys:
        return "fin"
    if {"cldf", "why_not", "motion", "authority_score", "normalized"} & keys:
        return "lex"
    return "lex"


def _get(d: Mapping[str, Any], path: list[str], default: Any = None) -> Any:
    cur: Any = d

    for k in path:
        if not isinstance(cur, Mapping) or k not in cur:  # type: ignore[arg-type]
            return default

        cur = cur[k]  # type: ignore[index]

    return cur


def _get(d: Mapping[str, Any], path: list[str], default: Any = None) -> Any:
    cur: Any = d

    for k in path:
        if not isinstance(cur, Mapping) or k not in cur:  # type: ignore[arg-type]
            return default

        cur = cur[k]  # type: ignore[index]

    return cur


def _has_counsel_signature(pco: Mapping[str, Any]) -> bool:
    sigs = pco.get("signatures") if isinstance(pco, Mapping) else None

    if not isinstance(sigs, list):
        return False

    for s in sigs:
        if isinstance(s, Mapping) and (s.get("role") == "counsel"):
            return True

    return False


def _sources_ok(pco: Mapping[str, Any], policy: Mapping[str, Any]) -> bool:
    srcs = pco.get("sources") if isinstance(pco, Mapping) else None

    if not isinstance(srcs, list) or len(srcs) == 0:
        return False

    for s in srcs:
        if not isinstance(s, Mapping):
            return False

        if not (isinstance(s.get("digest"), str) and s.get("digest")):
            return False

        if not (isinstance(s.get("retrieved_at"), str) and s.get("retrieved_at")):
            return False

    return True


def _derivations_ok(pco: Mapping[str, Any], policy: Mapping[str, Any]) -> bool:
    thr = _get(policy, ["publish_contract", "thresholds", "proofs"], {}) or {}

    allowed_formats = set(thr.get("formats_allowed", ["DRAT", "LRAT", "LFSC"]))

    allowed_solver = set(thr.get("solver_allowed", ["z3", "cvc5"]))

    derivs = pco.get("derivations") if isinstance(pco, Mapping) else None

    if not isinstance(derivs, list) or len(derivs) == 0:
        return False

    for d in derivs:
        if not isinstance(d, Mapping):
            return False

        if d.get("solver") not in allowed_solver:
            return False

        if d.get("proof_format") not in allowed_formats:
            return False

        if not (isinstance(d.get("artifact_digest"), str) and d.get("artifact_digest")):
            return False

    return True


def _repro_ok(pco: Mapping[str, Any], policy: Mapping[str, Any]) -> bool:
    req = bool(_get(policy, ["publish_contract", "thresholds", "reproducibility", "required"], False))

    if not req:
        return True

    r = pco.get("reproducibility") if isinstance(pco, Mapping) else None

    if not isinstance(r, Mapping):
        return False

    return all(isinstance(r.get(k), str) and r.get(k) for k in ("image", "image_digest", "seed"))


def _evaluate_decision(pco: Mapping[str, Any], policy: Mapping[str, Any], budget_tokens: int | None) -> str:
    thr = _get(policy, ["publish_contract", "thresholds", "risk"], {}) or {}

    e_max = float(thr.get("ece_max", 0.02))

    b_max = float(thr.get("brier_max", 0.10))

    a_max = float(thr.get("abstain_rate_max", 0.15))

    risk = pco.get("risk") if isinstance(pco, Mapping) else None

    if isinstance(risk, Mapping):
        try:
            ece = float(risk.get("ece", 0.0))

            brier = float(risk.get("brier", 0.0))

            abstain = float(risk.get("abstain_rate", 0.0))

        except Exception:
            return "CONDITIONAL"

        if ece > e_max or brier > b_max or abstain > a_max:
            return "ABSTAIN"

        # Policy checks: proofs, sources, reproducibility

        if not _derivations_ok(pco, policy):
            return "ABSTAIN"

        if not _sources_ok(pco, policy):
            return "ABSTAIN"

        if not _repro_ok(pco, policy):
            return "ABSTAIN"

        decision = "PUBLISH" if (budget_tokens or 0) > 0 else "PENDING"

        # Counsel signature required for PUBLISH/CONDITIONAL

        if decision in ("PUBLISH", "CONDITIONAL") and not _has_counsel_signature(pco):
            return "ABSTAIN"

        return decision

    return "CONDITIONAL"


@app.post("/v1/proofgate/publish", response_model=PublishResponse)
def publish(req: PublishRequest) -> PublishResponse:
    """

    Decision per Manifest v1.7: PUBLISH/CONDITIONAL/PENDING/ABSTAIN.

    """

    if req.pco is None:
        return PublishResponse(status="ABSTAIN", pco=None, ledger_ref=None)

    policy = req.policy or _load_policy_pack()

    # W9: TEE/Bunker profile (optional). If BUNKER=1, require attestation header.
    bunker_on = (os.getenv("BUNKER") or os.getenv("PROOFGATE_BUNKER") or "").strip() in {"1", "true", "True"}
    if bunker_on:
        # Attestation header stub: X-TEE-Attestation must be present and non-empty
        # Note: In this stubbed variant, we cannot access headers directly (no Request).
        # Allow PUBLISH path but require that PCO carries a tee.attested flag.
        try:
            tee = req.pco.get("tee") if isinstance(req.pco, dict) else None  # type: ignore[union-attr]
            if not (isinstance(tee, dict) and bool(tee.get("attested", False))):
                return PublishResponse(status="ABSTAIN", pco=req.pco, ledger_ref=None)
        except Exception:
            return PublishResponse(status="ABSTAIN", pco=req.pco, ledger_ref=None)

    # W9: Fine-grained role enforcement (optional)
    enforce_roles = (os.getenv("FINE_GRAINED_ROLES") or "").strip() in {"1", "true", "True"}

    decision = _evaluate_decision(req.pco, policy, req.budget_tokens)

    if enforce_roles and decision in ("PUBLISH", "CONDITIONAL"):
        # Governance‑aware enforcement: require at least one allowed role per governance pack
        try:
            sigs = req.pco.get("signatures") if isinstance(req.pco, dict) else None  # type: ignore[union-attr]
            roles_present = {s.get("role") for s in sigs if isinstance(s, dict)} if isinstance(sigs, list) else set()
            if not roles_present:
                decision = "ABSTAIN"
            else:
                gov = _load_governance_pack()
                dom = _infer_domain(req.pco)
                allow_map = ((gov.get("domains") or {}).get(dom) or {}).get("allow") or {}
                allowed = set(map(str, (allow_map.get("publish") or [])))
                # 'counsel' sygnatura jest wymagana osobno wcześniej; nie nadaje uprawnień publish
                if not (roles_present & allowed):
                    decision = "ABSTAIN"
        except Exception:
            decision = "ABSTAIN"

    ledger: str | None = None

    # On PUBLISH, persist a ledger event with a provenance hash of the PCO

    if decision == "PUBLISH":
        case_id = str(req.pco.get("case_id") or req.pco.get("rid") or "")

        doc_hash = compute_provenance_hash(req.pco, include_timestamp=False)

        rec = ledger_service.record_event(event_type="PCO_PUBLISH", case_id=case_id, document_hash=doc_hash)

        ledger = rec.get("chain_self")

    # Observe decision metrics (SLO)

    try:
        observe_decision(decision)

    except Exception:
        pass

    # OTel: correlate trace with PCO (best-effort)
    try:
        attrs = {}
        case_id = str(req.pco.get("case_id") or req.pco.get("rid") or "") if isinstance(req.pco, dict) else ""
        if case_id:
            attrs["pco.case_id"] = case_id
        attrs["pco.decision"] = decision
        set_span_attrs(attrs)
    except Exception:
        pass

    return PublishResponse(status=decision, pco=req.pco, ledger_ref=ledger)


# === I/O / ENDPOINTS ===

# Cache OpenAPI JSON in-memory to reduce overhead
_openapi_schema_cache = None


def _cached_openapi():  # type: ignore[override]
    global _openapi_schema_cache
    if _openapi_schema_cache:
        return _openapi_schema_cache
    _openapi_schema_cache = get_openapi(
        title="ProofGate",
        version=__version__,
        routes=app.routes,
    )
    return _openapi_schema_cache


app.openapi = _cached_openapi  # type: ignore[assignment]

# === TESTY / TESTS ===
