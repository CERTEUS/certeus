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
import json
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
from services.ledger_service.ledger import compute_provenance_hash, ledger_service

try:  # optional: FROST aggregator
    from security.frost import verify_quorum
except Exception:  # pragma: no cover - optional

    def verify_quorum(_obj):  # type: ignore
        return False


try:  # optional: RA helpers for TEE status
    from security.ra import (
        attestation_from_env,
        extract_fingerprint,
        verify_fingerprint,
    )
except Exception:  # pragma: no cover - optional

    def attestation_from_env():  # type: ignore
        return None

    def extract_fingerprint(_obj):  # type: ignore
        class _FP:
            def to_dict(self):
                return {}

        return _FP()

    def verify_fingerprint(_obj):  # type: ignore
        return False


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


class RtbfAppealRequest(BaseModel):
    case_id: str = Field(..., description="Case identifier (RID or CASE_ID)")
    reason: str | None = Field(default=None, description="Optional appeal reason")


class RtbfAppealResponse(BaseModel):
    status: str
    case_id: str
    reason: str | None = None


class RtbfEraseRequest(BaseModel):
    case_id: str = Field(..., description="Case identifier (RID or CASE_ID)")


class RtbfEraseResponse(BaseModel):
    status: str
    case_id: str


# === LOGIKA / LOGIC ===

app = FastAPI(title="ProofGate", version=__version__)
setup_fastapi_otel(app)


@app.get("/healthz")
def healthz() -> dict[str, Any]:
    return {"ok": True, "service": "proofgate-stub"}


@app.get("/v1/tee/status")
def tee_status() -> dict[str, Any]:
    """PL/EN: Report bunker/TEE status for UI badges (best-effort)."""
    bunker_on = (os.getenv("BUNKER") or os.getenv("PROOFGATE_BUNKER") or "").strip() in {"1", "true", "True", "on"}
    ra_req = (os.getenv("TEE_RA_REQUIRE") or "").strip() in {"1", "true", "True", "on"}
    att = attestation_from_env()
    fp = None
    attested = False
    try:
        if att:
            attested = True
            fpo = extract_fingerprint(att)
            fpd = getattr(fpo, "to_dict", lambda: {})()
            if isinstance(fpd, dict):
                # validate shape best-effort
                if verify_fingerprint(fpd):
                    fp = fpd
                else:
                    fp = {k: fpd.get(k) for k in ("vendor", "product", "measurement") if k in fpd}
    except Exception:
        attested = False
        fp = None
    return {
        "bunker_on": bunker_on,
        "ra_required": ra_req,
        "attested": bool(attested),
        "ra": fp,
    }


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


_RTBF_STORE = _repo_root() / "out" / "rtbf_erased.json"
_RTBF_APPEALS = _repo_root() / "out" / "rtbf_appeals.json"


def _load_rtbf_store() -> set[str]:
    try:
        import json

        data = json.loads(_RTBF_STORE.read_text(encoding="utf-8")) if _RTBF_STORE.exists() else []
        return {str(x) for x in (data or [])}
    except Exception:
        return set()


def _save_rtbf_store(items: set[str]) -> None:
    try:
        import json

        _RTBF_STORE.parent.mkdir(parents=True, exist_ok=True)
        _RTBF_STORE.write_text(json.dumps(sorted(items), indent=2), encoding="utf-8")
    except Exception:
        pass


def _now_iso() -> str:
    import time

    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _load_appeals() -> dict[str, dict[str, str]]:
    try:
        import json

        data = {} if not _RTBF_APPEALS.exists() else json.loads(_RTBF_APPEALS.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            return {}
        # Ensure mapping of case -> {received_at, reason}
        out: dict[str, dict[str, str]] = {}
        for k, v in data.items():
            if isinstance(v, dict):
                rec = {"received_at": str(v.get("received_at") or _now_iso())}
                if v.get("reason"):
                    rec["reason"] = str(v["reason"])  # type: ignore[index]
                out[str(k)] = rec
        return out
    except Exception:
        return {}


def _save_appeals(data: dict[str, dict[str, str]]) -> None:
    try:
        import json

        _RTBF_APPEALS.parent.mkdir(parents=True, exist_ok=True)
        _RTBF_APPEALS.write_text(json.dumps(data, indent=2), encoding="utf-8")
    except Exception:
        pass


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


def _load_json(path: Path) -> dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _validate_pco_extensions(pco: Mapping[str, Any]) -> list[str]:
    """PL/EN: Opcjonalna walidacja rozszerzeń PCO (report-only).

    Aktualnie wspiera SEC‑PCO pod kluczami `security` lub `sec`.
    Zwraca listę błędów walidacji (pusta ⇒ brak lub OK).
    """
    errs: list[str] = []
    try:
        # lazy import; brak zależności nie blokuje publikacji
        from jsonschema import Draft7Validator  # type: ignore

        repo = _repo_root()
        sec_schema = _load_json(repo / "schemas" / "security_pco_v0.1.json")
        v_sec = Draft7Validator(sec_schema) if sec_schema else None  # type: ignore[call-arg]

        sec_obj: Any = None
        if isinstance(pco.get("security"), Mapping):
            sec_obj = pco.get("security")
        elif isinstance(pco.get("sec"), Mapping):
            sec_obj = pco.get("sec")

        if v_sec is not None and isinstance(sec_obj, Mapping):
            for err in v_sec.iter_errors(sec_obj):
                errs.append(f"SEC schema: {err.message}")
    except Exception:
        # report-only: nie blokujemy, ignorujemy błędy narzędzi
        return errs

    return errs


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
    req = bool(
        _get(
            policy,
            ["publish_contract", "thresholds", "reproducibility", "required"],
            False,
        )
    )

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
        # Attestation stub: in this variant we cannot access headers directly (no Request).
        # Require that PCO carries a tee.attested flag. If TEE_RA_REQUIRE=1, also require
        # a minimal RA fingerprint under tee.ra {vendor,product,measurement}.
        try:
            tee = req.pco.get("tee") if isinstance(req.pco, dict) else None  # type: ignore[union-attr]
            if not (isinstance(tee, dict) and bool(tee.get("attested", False))):
                return PublishResponse(status="ABSTAIN", pco=req.pco, ledger_ref=None)
            if (os.getenv("TEE_RA_REQUIRE") or "").strip() in {"1", "true", "True"}:
                ra = tee.get("ra") if isinstance(tee, dict) else None
                ok_ra = (
                    isinstance(ra, dict)
                    and isinstance(ra.get("vendor"), str)
                    and isinstance(ra.get("product"), str)
                    and isinstance(ra.get("measurement"), str)
                )
                if not ok_ra:
                    return PublishResponse(status="ABSTAIN", pco=req.pco, ledger_ref=None)
        except Exception:
            return PublishResponse(status="ABSTAIN", pco=req.pco, ledger_ref=None)

    # W9: Decision (base), then optional gates (PQ/roles/FROST)
    decision = _evaluate_decision(req.pco, policy, req.budget_tokens)

    # W9: PQ-crypto gate (optional, stub)
    pq_require = (os.getenv("PQCRYPTO_REQUIRE") or "").strip() in {"1", "true", "True"}
    pq_ready_env = (os.getenv("PQCRYPTO_READY") or "").strip() in {"1", "true", "True"}

    if pq_require and decision != "ABSTAIN":
        try:
            pq_ready_pco = False
            if isinstance(req.pco, dict):
                crypto = req.pco.get("crypto") if isinstance(req.pco.get("crypto"), dict) else {}
                pq = crypto.get("pq") if isinstance(crypto, dict) else None
                pq_ready_pco = bool((pq or {}).get("ready", False))
            if not (pq_ready_pco or pq_ready_env):
                decision = "ABSTAIN"
        except Exception:
            decision = "ABSTAIN"

    # W9: Fine-grained role enforcement (optional)
    enforce_roles = (os.getenv("FINE_GRAINED_ROLES") or "").strip() in {
        "1",
        "true",
        "True",
    }

    # Opcjonalna walidacja PCO (report-only)
    if (os.getenv("VALIDATE_PCO") or "").strip() in {"1", "true", "True"}:
        try:
            pco_errs = _validate_pco_extensions(req.pco)
            if pco_errs:
                print("[ProofGate] PCO validation warnings:")
                for e in pco_errs:
                    print(" -", e)
        except Exception:
            # report-only
            pass

    decision = _evaluate_decision(req.pco, policy, req.budget_tokens)

    # FROST 2-of-3 (optional enforce)
    frost_env = (os.getenv("REQUIRE_COSIGN_ATTESTATIONS") or os.getenv("FROST_REQUIRE") or "").strip()
    frost_require = frost_env in {"1", "true", "True"}
    if frost_require and decision in ("PUBLISH", "CONDITIONAL"):
        try:
            cos = req.pco.get("cosign") if isinstance(req.pco, dict) else None  # type: ignore[union-attr]
            if not (isinstance(cos, dict) and verify_quorum(cos)):
                decision = "ABSTAIN"
        except Exception:
            decision = "ABSTAIN"

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

    # Require cryptographic signatures (Ed25519 and/or PQ) if requested
    if decision in ("PUBLISH", "CONDITIONAL") and (os.getenv("SIGNATURES_REQUIRE") or "").strip() in {
        "1",
        "true",
        "True",
    }:
        try:
            # Compute stable provenance hash
            _doc_hash = compute_provenance_hash(req.pco, include_timestamp=False)
            from core.pco.crypto import b64u_decode, ed25519_verify_b64u  # type: ignore

            # Ed25519 verify (if ed25519 block present or env pub provided)
            ed_ok = True
            try:
                src = req.pco if isinstance(req.pco, dict) else {}
                ed = (src.get("crypto") or {}) if isinstance(src, dict) else {}
                ed = ed.get("ed25519") if isinstance(ed, dict) else None
                sig_b64 = str(ed.get("sig_b64")) if isinstance(ed, dict) and ed.get("sig_b64") else None
                pub_b64 = str(ed.get("pub_b64")) if isinstance(ed, dict) and ed.get("pub_b64") else None
                # Prefer env pubkey if present
                ev_pub_hex = (os.getenv("ED25519_PUBKEY_HEX") or "").strip()
                ev_pub_b64 = (os.getenv("ED25519_PUBKEY_B64URL") or os.getenv("ED25519_PUBKEY_B64U") or "").strip()
                if sig_b64:
                    if ev_pub_hex:
                        ed25519_verify_b64u(bytes.fromhex(ev_pub_hex), sig_b64, _doc_hash)
                    elif ev_pub_b64:
                        ed25519_verify_b64u(b64u_decode(ev_pub_b64), sig_b64, _doc_hash)
                    elif pub_b64:
                        ed25519_verify_b64u(b64u_decode(pub_b64), sig_b64, _doc_hash)
                    else:
                        ed_ok = False
                else:
                    # Require presence if signatures are required
                    ed_ok = False
            except Exception:
                ed_ok = False

            # PQ verify via pyoqs (if available and pq block present)
            pq_ok = True
            try:
                src = req.pco if isinstance(req.pco, dict) else {}
                pq = (src.get("crypto") or {}) if isinstance(src, dict) else {}
                pq = pq.get("pq") if isinstance(pq, dict) else None
                if isinstance(pq, dict) and pq.get("sig_b64"):
                    import base64 as _b64

                    from security import pq_mldsa as _pq  # type: ignore

                    sig = _b64.urlsafe_b64decode(
                        (str(pq.get("sig_b64")) + "=" * (-len(str(pq.get("sig_b64"))) % 4)).encode("ascii")
                    )
                    pub = str(pq.get("pub_b64") or os.getenv("PQ_MLDSA_PK_B64URL") or "")
                    if not pub:
                        pq_ok = False
                    else:
                        pk = _b64.urlsafe_b64decode((pub + "=" * (-len(pub) % 4)).encode("ascii"))
                        alg = str(pq.get("alg") or os.getenv("PQ_MLDSA_ALG") or "Dilithium3")
                        pq_ok = _pq.verify(_doc_hash.encode("utf-8"), sig, pk, alg=alg)
                else:
                    pq_ok = False
            except Exception:
                pq_ok = False

            if not (ed_ok and pq_ok):
                decision = "ABSTAIN"
        except Exception:
            decision = "ABSTAIN"

    # Optionally embed TEE RA fingerprint into PCO (when bunker is on and attestation present)
    pco_out = req.pco
    if bunker_on and isinstance(req.pco, dict):
        try:
            att = attestation_from_env()
            if att:
                fp = extract_fingerprint(att).to_dict()
                # Merge into tee block without overwriting explicit client-provided RA
                tee = dict(req.pco.get("tee") or {})
                tee.setdefault("attested", True)
                tee.setdefault("ra", fp)
                pco_out = dict(req.pco)
                pco_out["tee"] = tee
        except Exception:
            pass

    # Optionally embed PQ-crypto (ML-DSA) signature over provenance hash
    if isinstance(req.pco, dict):
        try:
            # Canonical provenance hash (stable)
            _doc_hash = compute_provenance_hash(req.pco, include_timestamp=False)

            def _b64u(b: bytes) -> str:
                import base64 as _b64

                return _b64.urlsafe_b64encode(b).decode("ascii").rstrip("=")

            sk_b64 = (os.getenv("PQ_MLDSA_SK_B64URL") or "").strip()
            pk_b64 = (os.getenv("PQ_MLDSA_PK_B64URL") or "").strip()
            alg = (os.getenv("PQ_MLDSA_ALG") or "Dilithium3").strip()
            pq_ready_env = (os.getenv("PQCRYPTO_READY") or "").strip() in {"1", "true", "True"}

            pq_block: dict[str, Any] = {"ready": bool(pq_ready_env)}
            if sk_b64:
                try:
                    import base64 as _b64

                    from security import pq_mldsa as _pq

                    pad = "=" * (-len(sk_b64) % 4)
                    sk_raw = _b64.urlsafe_b64decode((sk_b64 + pad).encode("ascii"))
                    sig = _pq.sign(_doc_hash.encode("utf-8"), sk_raw, alg=alg)
                    pq_block.update({"alg": alg, "sig_b64": _b64u(sig)})
                    if pk_b64:
                        pq_block["pub_b64"] = pk_b64
                    pq_block["ready"] = True
                except Exception:
                    # Keep env marker only
                    pass
            # Merge into crypto.pq without clobbering explicit client-provided fields
            pco_out = dict(pco_out or req.pco)
            crypto = dict(pco_out.get("crypto") or {})
            pq_merged = dict(crypto.get("pq") or {})
            for k, v in pq_block.items():
                pq_merged.setdefault(k, v)
            crypto["pq"] = pq_merged
            pco_out["crypto"] = crypto
        except Exception:
            pass

    # Optionally embed Ed25519 signature over provenance hash
    if isinstance(req.pco, dict):
        try:
            _doc_hash = compute_provenance_hash(req.pco, include_timestamp=False)
            from core.pco.crypto import ed25519_sign_b64u  # type: ignore

            sk_hex = (os.getenv("ED25519_SK_HEX") or "").strip()
            sk_b64 = (os.getenv("ED25519_SK_B64URL") or os.getenv("ED25519_SK_B64U") or "").strip()
            pk_b64 = (os.getenv("ED25519_PUBKEY_B64URL") or os.getenv("ED25519_PUBKEY_B64U") or "").strip()

            def _b64u_to_bytes(s: str) -> bytes:
                import base64 as _b64

                return _b64.urlsafe_b64decode((s + "=" * (-len(s) % 4)).encode("ascii"))

            sk_bytes: bytes | None = None
            if sk_hex:
                try:
                    sk_bytes = bytes.fromhex(sk_hex)
                except Exception:
                    sk_bytes = None
            if sk_bytes is None and sk_b64:
                try:
                    sk_bytes = _b64u_to_bytes(sk_b64)
                except Exception:
                    sk_bytes = None
            if sk_bytes:
                try:
                    sig = ed25519_sign_b64u(sk_bytes, _doc_hash)
                    crypto = dict(pco_out.get("crypto") or {})
                    ed = dict(crypto.get("ed25519") or {})
                    ed.setdefault("sig_b64", sig)
                    if pk_b64:
                        ed.setdefault("pub_b64", pk_b64)
                    crypto["ed25519"] = ed
                    pco_out = dict(pco_out)
                    pco_out["crypto"] = crypto
                except Exception:
                    pass
        except Exception:
            pass

    ledger: str | None = None

    # On PUBLISH, persist a ledger event with a provenance hash of the PCO

    if decision == "PUBLISH":
        case_id = str((pco_out or {}).get("case_id") or (pco_out or {}).get("rid") or "")

        # Ledger must reflect the original client-provided PCO (stable hash)
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

    return PublishResponse(status=decision, pco=pco_out, ledger_ref=ledger)


# === I/O / ENDPOINTS ===


@app.post("/v1/rtbf/appeal", response_model=RtbfAppealResponse)
def rtbf_appeal(req: RtbfAppealRequest) -> RtbfAppealResponse:
    """
    PL: Rejestruje odwołanie RTBF (stub); zwraca status RECEIVED.
    EN: Registers an RTBF appeal (stub); returns status RECEIVED.
    """

    appeals = _load_appeals()
    appeals[req.case_id] = {
        "received_at": _now_iso(),
        **({"reason": req.reason} if req.reason else {}),
    }
    _save_appeals(appeals)
    return RtbfAppealResponse(status="RECEIVED", case_id=req.case_id, reason=req.reason)


@app.post("/v1/rtbf/erase", response_model=RtbfEraseResponse)
def rtbf_erase(req: RtbfEraseRequest) -> RtbfEraseResponse:
    """
    PL: Zaznacza sprawę jako usuniętą (stub, brak dostępu do prywatnych danych w ProofGate).
    EN: Marks case as erased (stub; ProofGate has no access to private data).
    """

    items = _load_rtbf_store()
    items.add(req.case_id)
    _save_rtbf_store(items)
    return RtbfEraseResponse(status="ERASED", case_id=req.case_id)


@app.get("/v1/rtbf/erased/{case_id}")
def rtbf_erased(case_id: str) -> dict[str, bool]:
    """PL/EN: Returns whether a case is marked as erased (best-effort)."""

    items = _load_rtbf_store()
    return {"erased": case_id in items}


@app.get("/v1/rtbf/appeal_sla/{case_id}")
def rtbf_appeal_sla(case_id: str) -> dict[str, str | float | bool]:
    """
    PL: Zwraca szczegóły SLA dla odwołania (received_at, due_by). Domyślnie 72h.
    EN: Returns SLA details for an appeal (received_at, due_by). Default 72h.
    """

    import datetime as _dt

    appeals = _load_appeals()
    rec = appeals.get(case_id)
    sla_h = float(os.getenv("RTBF_APPEAL_SLA_HOURS", "72") or 72)
    if not rec:
        return {"present": False, "sla_hours": sla_h}
    try:
        received_at = rec.get("received_at") or _now_iso()
        t = _dt.datetime.strptime(received_at, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=_dt.UTC)
    except Exception:
        t = _dt.datetime.now(tz=_dt.UTC)
        received_at = _now_iso()
    due = t + _dt.timedelta(hours=sla_h)
    return {
        "present": True,
        "received_at": received_at,
        "sla_hours": sla_h,
        "due_by": due.strftime("%Y-%m-%dT%H:%M:%SZ"),
    }


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
