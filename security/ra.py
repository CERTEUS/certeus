#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: security/ra.py                                       |
# | ROLE: TEE attestation helpers                                |
# | PLIK: security/ra.py                                       |
# | ROLA: Pomocniki atestacji TEE                                |
# +-------------------------------------------------------------+

"""
PL: Pomocnicze funkcje do sygnalizacji TEE oraz generowania odcisku RA.

EN: Helpers for TEE signalling and computing RA fingerprint.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from typing import Any


def tee_enabled() -> bool:
    """Return True if TEE signalling is enabled via env."""

    val = (os.getenv("TEE_ENABLED") or os.getenv("BUNKER") or "").strip()
    return val in {"1", "true", "True"}


def load_attestation() -> dict[str, Any]:
    """Load attestation JSON (best-effort).

    Sources (first hit wins):
    - ENV `TEE_ATTESTATION_JSON` (inline JSON string)
    - Repo file `security/bunker/attestation.json`
    - Fallback stub
    """

    env = os.getenv("TEE_ATTESTATION_JSON")
    if env and env.strip().startswith("{"):
        try:
            return json.loads(env)
        except Exception:
            pass
    p = Path(__file__).resolve().parent / "bunker" / "attestation.json"
    try:
        if p.exists():
            return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        pass
    return {
        "provider": "TEE-STUB",
        "platform": "SIMULATED",
        "quote": "",
        "attester": "local",
        "ts": "",
    }


def ra_fingerprint() -> dict[str, Any]:
    """Compute fingerprint from attestation JSON.

    Uses sha256 over stable JSON (sorted keys) or `quote` if present.
    """

    att = load_attestation()
    base = att.get("quote") or json.dumps(att, sort_keys=True, separators=(",", ":"))
    fp = hashlib.sha256(str(base).encode("utf-8")).hexdigest()
    return {
        "provider": str(att.get("provider") or ""),
        "platform": str(att.get("platform") or ""),
        "fingerprint": f"sha256:{fp}",
        "ts": str(att.get("ts") or ""),
    }


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
