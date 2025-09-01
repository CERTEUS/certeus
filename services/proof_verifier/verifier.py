# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/proof_verifier/verifier.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/proof_verifier/verifier.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from dataclasses import dataclass

import hashlib

import logging

import os

import re

import subprocess

from typing import Any

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===
class VerificationResult:
    ok: bool

    proof_hash: str

    details: dict[str, Any]

# === LOGIKA / LOGIC ===





@dataclass




_LFSC_HEADER_RE = re.compile(r"\(\s*lfsc\b", re.IGNORECASE)

_DRAT_HINT_RE = re.compile(r"^(p\s+drat|d\s+|\s*c\s*)", re.IGNORECASE | re.MULTILINE)


def _sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def verify_lfsc(text: str) -> VerificationResult:
    data = text.encode("utf-8")

    mock = os.getenv("PROOF_VERIFIER_MOCK")

    if mock == "lfsc_ok":
        return VerificationResult(ok=True, proof_hash=_sha256_hex(data), details={"verifier": "mock:lfsc-ok"})

    if mock == "lfsc_fail":
        return VerificationResult(ok=False, proof_hash=_sha256_hex(data), details={"verifier": "mock:lfsc-fail"})

    cmd = os.getenv("CVC5_CMD")

    if cmd:
        try:
            debug = os.getenv("PROOF_VERIFY_DEBUG") == "1"

            if debug:
                logging.getLogger(__name__).debug("LFSC verify: running %s", cmd)

            proc = subprocess.run(
                cmd.split(),
                input=data,
                capture_output=True,
                timeout=float(os.getenv("PROOF_VERIFY_TIMEOUT_SECS", "10")),
                check=False,
            )

            ok = proc.returncode == 0

            if debug:
                out = (proc.stdout or b"").decode("utf-8", errors="ignore")[:200]

                err = (proc.stderr or b"").decode("utf-8", errors="ignore")[:200]

                logging.getLogger(__name__).debug("LFSC verify rc=%s out='%s' err='%s'", proc.returncode, out, err)

            return VerificationResult(
                ok=ok, proof_hash=_sha256_hex(data), details={"verifier": "external:cvc5", "rc": proc.returncode}
            )

        except Exception as e:
            if os.getenv("PROOF_VERIFY_DEBUG") == "1":
                logging.getLogger(__name__).exception("LFSC external verifier error: %s", e)

            return VerificationResult(
                ok=False, proof_hash=_sha256_hex(data), details={"verifier": f"external:cvc5:error:{e}"}
            )

    ok = bool(text.strip()) and bool(_LFSC_HEADER_RE.search(text))

    return VerificationResult(ok=ok, proof_hash=_sha256_hex(data), details={"verifier": "internal:lfsc-check"})


def verify_drat(text: str) -> VerificationResult:
    if text is None:
        return VerificationResult(ok=False, proof_hash="", details={"verifier": "internal:drat-check"})

    data = text.encode("utf-8")

    mock = os.getenv("PROOF_VERIFIER_MOCK")

    if mock == "drat_ok":
        return VerificationResult(ok=True, proof_hash=_sha256_hex(data), details={"verifier": "mock:drat-ok"})

    if mock == "drat_fail":
        return VerificationResult(ok=False, proof_hash=_sha256_hex(data), details={"verifier": "mock:drat-fail"})

    cmd = os.getenv("DRAT_CHECK_CMD")

    if cmd:
        try:
            debug = os.getenv("PROOF_VERIFY_DEBUG") == "1"

            if debug:
                logging.getLogger(__name__).debug("DRAT verify: running %s", cmd)

            proc = subprocess.run(
                cmd.split(),
                input=data,
                capture_output=True,
                timeout=float(os.getenv("PROOF_VERIFY_TIMEOUT_SECS", "10")),
                check=False,
            )

            ok = proc.returncode == 0

            if debug:
                out = (proc.stdout or b"").decode("utf-8", errors="ignore")[:200]

                err = (proc.stderr or b"").decode("utf-8", errors="ignore")[:200]

                logging.getLogger(__name__).debug("DRAT verify rc=%s out='%s' err='%s'", proc.returncode, out, err)

            return VerificationResult(
                ok=ok, proof_hash=_sha256_hex(data), details={"verifier": "external:drat", "rc": proc.returncode}
            )

        except Exception as e:
            if os.getenv("PROOF_VERIFY_DEBUG") == "1":
                logging.getLogger(__name__).exception("DRAT external verifier error: %s", e)

            return VerificationResult(
                ok=False, proof_hash=_sha256_hex(data), details={"verifier": f"external:drat:error:{e}"}
            )

    ok = bool(text.strip()) and bool(_DRAT_HINT_RE.search(text))

    return VerificationResult(ok=ok, proof_hash=_sha256_hex(data), details={"verifier": "internal:drat-check"})



# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

