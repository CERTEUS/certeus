#!/usr/bin/env python3
# +-------------------------------------------------------------+
# | CERTEUS Control System | ForgeHeader v3 - Enterprise     |
# | FILE: workspaces/certeus/security/ra.py                                      |
# | ROLE: Implementation file                                        |
# +-------------------------------------------------------------+


"""
PL: Remote Attestation (TEE) — minimalna obsługa odcisku RA na potrzeby CI/ProofGate.
EN: Remote Attestation (TEE) — minimal RA fingerprint utilities for CI/ProofGate.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class RAFingerprint:
    vendor: str
    product: str
    measurement: str  # hex digest of claims
    hwid: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _h_json(obj: Any) -> str:
    s = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(s).hexdigest()


def parse_attestation_json(p: str | os.PathLike[str]) -> dict[str, Any]:
    path = Path(p)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("attestation must be JSON object")
    return data


def extract_fingerprint(attestation: dict[str, Any]) -> RAFingerprint:
    vendor = str(attestation.get("vendor") or attestation.get("tee_vendor") or "unknown").strip()
    product = str(attestation.get("product") or attestation.get("tee") or "unknown").strip()
    hwid = attestation.get("hwid") or attestation.get("device_id")
    claims = attestation.get("claims") if isinstance(attestation.get("claims"), dict) else attestation
    meas = _h_json(claims)
    return RAFingerprint(
        vendor=vendor,
        product=product,
        measurement=meas,
        hwid=str(hwid) if hwid else None,
    )


def verify_fingerprint(obj: dict[str, Any]) -> bool:
    try:
        vendor = obj.get("vendor")
        product = obj.get("product")
        measurement = obj.get("measurement")
        return all(isinstance(x, str) and x for x in (vendor, product, measurement)) and len(measurement) == 64
    except Exception:
        return False


def attestation_from_env() -> dict[str, Any] | None:
    """
    Best-effort attestation loader.

    Priority:
    1) BUNKER_ATTESTATION_PATH -> JSON file
    2) security/bunker/attestation.json (repo default)
    3) If BUNKER=1 but no file available, synthesize minimal stub so that
       upstream status/reporting can proceed (report-only contexts). The
       stub still yields a deterministic measurement via extract_fingerprint.
    """

    # 1) Explicit path via env
    cand_env = os.getenv("BUNKER_ATTESTATION_PATH")
    if cand_env:
        try:
            p = Path(cand_env)
            if p.exists():
                return parse_attestation_json(p)
        except Exception:
            pass

    # 2) Repository default
    try:
        p_def = Path("security/bunker/attestation.json")
        if p_def.exists():
            return parse_attestation_json(p_def)
    except Exception:
        pass

    # 3) Synthesized minimal attestation if bunker is on
    bunker_on = (os.getenv("BUNKER") or os.getenv("PROOFGATE_BUNKER") or "").strip().lower() in {
        "1",
        "true",
        "on",
    }
    if bunker_on:
        return {"vendor": "unknown", "product": "unknown", "claims": {}}

    return None
