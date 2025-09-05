#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/pnip.py                        |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/pnip.py                        |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: PNIP – Proof-Native Input Profile. Walidacja podstawowych pól na wejściu
    (hash dokumentu, jurysdykcja, polityka). Błędne PNIP => 400 + PCO błędu.

EN: PNIP – Proof-Native Input Profile. Validate basic input (document hash,
    jurisdiction, policy). On invalid PNIP => 400 + PCO error.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from pathlib import Path
from typing import Any

from fastapi import HTTPException, Request
from pydantic import BaseModel, Field
import yaml

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

class PNIP(BaseModel):
    document_hash: str = Field(..., min_length=7)
    juris_country: str = Field(..., min_length=2, max_length=2)
    juris_domain: str = Field(..., min_length=2, max_length=32)
    policy_pack_id: str = Field(..., min_length=3)

# === LOGIKA / LOGIC ===

def _policy_pack_id() -> str:
    # Read from policies/pco/policy_pack.yaml (meta.id)
    try:
        p = Path(__file__).resolve().parents[3] / "policies" / "pco" / "policy_pack.yaml"
        doc = yaml.safe_load(p.read_text(encoding="utf-8"))
        mid = str(((doc or {}).get("meta") or {}).get("id") or "pco-policy-pack")
        return mid
    except Exception:
        return "pco-policy-pack"

def _parse_jurisdiction(header_val: str | None) -> tuple[str, str]:
    # Format: "CC[:domain]" e.g., "PL" or "PL:finance"
    default_country = os.getenv("DEFAULT_JURIS_COUNTRY", "PL").upper()
    default_domain = os.getenv("DEFAULT_JURIS_DOMAIN", "other").lower()
    if not header_val:
        return default_country, default_domain
    val = header_val.strip()
    if ":" in val:
        cc, dom = val.split(":", 1)
    else:
        cc, dom = val, default_domain
    cc = cc.strip().upper()[:2]
    dom = dom.strip().lower()
    # allow only letters, dashes
    if not (len(cc) == 2 and cc.isalpha()):
        cc = default_country
    if not dom.replace("-", "").isalpha():
        dom = default_domain
    return cc, dom

def _validate_hash(h: str) -> bool:
    if not isinstance(h, str) or ":" not in h:
        return False
    algo, hx = h.split(":", 1)
    if algo.lower() != "sha256":
        return False
    if len(hx) != 64:
        return False
    try:
        int(hx, 16)
        return True
    except Exception:
        return False

def make_pco_error(code: str, message: str, *, ctx: dict[str, Any] | None = None) -> dict[str, Any]:
    return {
        "version": "0.2",
        "status": "ERROR",
        "error": {"code": code, "message": message, "context": (ctx or {})},
    }

def validate_pnip_request(request: Request, *, body: dict[str, Any] | None, strict: bool = False) -> PNIP | None:
    # Headers precedence, fallback to body keys
    jhdr = request.headers.get("X-Jurisdiction") or request.headers.get("x-jurisdiction")
    juris_country, juris_domain = _parse_jurisdiction(jhdr)
    policy_hdr = (
        request.headers.get("X-Policy-Pack-ID")
        or request.headers.get("x-policy-pack-id")
        or request.headers.get("X-Norm-Pack-ID")
        or request.headers.get("x-norm-pack-id")
    )
    policy_pack_id = (policy_hdr or _policy_pack_id()).strip()
    doc_hash = None
    if body is not None:
        dh = body.get("document_hash") or body.get("hash")
        if isinstance(dh, str):
            doc_hash = dh

    pnip = PNIP(
        document_hash=doc_hash or "sha256:" + ("0" * 64),  # placeholder if missing in non-strict mode
        juris_country=juris_country,
        juris_domain=juris_domain,
        policy_pack_id=policy_pack_id,
    )

    # Validate under rules
    ok_hash = _validate_hash(pnip.document_hash)
    ok_cc = len(pnip.juris_country) == 2 and pnip.juris_country.isalpha()
    ok_dom = pnip.juris_domain.replace("-", "").isalpha()
    ok_pol = pnip.policy_pack_id == _policy_pack_id()

    if strict and (not ok_hash or not ok_cc or not ok_dom or not ok_pol):
        err = make_pco_error(
            code="PNIP_INVALID",
            message="Invalid PNIP: hash/jurisdiction/policy",
            ctx={
                "ok_hash": ok_hash,
                "ok_jurisdiction": ok_cc and ok_dom,
                "ok_policy": ok_pol,
            },
        )
        raise HTTPException(status_code=400, detail=err)

    return pnip if strict or ok_hash else None

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
