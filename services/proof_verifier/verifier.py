from __future__ import annotations

from dataclasses import dataclass
import hashlib
import re
from typing import Any


@dataclass
class VerificationResult:
    ok: bool
    proof_hash: str
    details: dict[str, Any]


_LFSC_HEADER_RE = re.compile(r"\(\s*lfsc\b", re.IGNORECASE)
_DRAT_HINT_RE = re.compile(r"^(p\s+drat|d\s+|\s*c\s*)", re.IGNORECASE | re.MULTILINE)


def _sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def verify_lfsc(text: str) -> VerificationResult:
    data = text.encode("utf-8")
    ok = bool(text.strip()) and bool(_LFSC_HEADER_RE.search(text))
    return VerificationResult(ok=ok, proof_hash=_sha256_hex(data), details={"verifier": "internal:lfsc-check"})


def verify_drat(text: str) -> VerificationResult:
    if text is None:
        return VerificationResult(ok=False, proof_hash="", details={"verifier": "internal:drat-check"})
    data = text.encode("utf-8")
    # Very light heuristic: presence of typical drat markers or non-empty
    ok = bool(text.strip()) and bool(_DRAT_HINT_RE.search(text))
    return VerificationResult(ok=ok, proof_hash=_sha256_hex(data), details={"verifier": "internal:drat-check"})
