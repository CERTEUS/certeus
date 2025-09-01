"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/proofgate/app.py                           |

# | ROLE: Project module.                                       |

# | PLIK: services/proofgate/app.py                           |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path
from typing import Any

from fastapi import FastAPI
from pydantic import BaseModel, Field
import yaml

from core.version import __version__
from monitoring.metrics_slo import observe_decision
from services.ledger_service.ledger import (
    compute_provenance_hash,
    ledger_service,
)

app = FastAPI(title="ProofGate", version=__version__)


@app.get("/healthz")
def healthz() -> dict[str, Any]:
    return {"ok": True, "service": "proofgate-stub"}


class PublishRequest(BaseModel):
    pco: dict[str, Any] | None = Field(default=None, description="Proof-Carrying Object")

    policy: dict[str, Any] | None = None

    budget_tokens: int | None = None


class PublishResponse(BaseModel):
    status: str

    pco: dict[str, Any] | None = None

    ledger_ref: str | None = None


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def _load_policy_pack() -> dict[str, Any]:
    p = _repo_root() / "policies" / "pco" / "policy_pack.yaml"

    try:
        return yaml.safe_load(p.read_text(encoding="utf-8")) or {}

    except Exception:
        return {}


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

    decision = _evaluate_decision(req.pco, policy, req.budget_tokens)

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

    return PublishResponse(status=decision, pco=req.pco, ledger_ref=ledger)
