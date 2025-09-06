#!/usr/bin/env python3

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
    vendor = str(
        attestation.get("vendor") or attestation.get("tee_vendor") or "unknown"
    ).strip()
    product = str(
        attestation.get("product") or attestation.get("tee") or "unknown"
    ).strip()
    hwid = attestation.get("hwid") or attestation.get("device_id")
    claims = (
        attestation.get("claims")
        if isinstance(attestation.get("claims"), dict)
        else attestation
    )
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
        return (
            all(isinstance(x, str) and x for x in (vendor, product, measurement))
            and len(measurement) == 64
        )
    except Exception:
        return False


def attestation_from_env() -> dict[str, Any] | None:
    cand = os.getenv("BUNKER_ATTESTATION_PATH") or (
        Path("security/bunker/attestation.json").as_posix()
    )
    try:
        p = Path(cand)
        if p.exists():
            return parse_attestation_json(p)
    except Exception:
        return None
    return None
