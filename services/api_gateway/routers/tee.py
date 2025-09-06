#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/tee.py                  |
# | ROLE: TEE status endpoint for UI badges                    |
# +-------------------------------------------------------------+

from __future__ import annotations

import os
from typing import Any

from fastapi import APIRouter

try:  # optional RA helpers
    from security.ra import (
        attestation_from_env,
        extract_fingerprint,
        verify_fingerprint,
    )
except Exception:  # pragma: no cover

    def attestation_from_env():  # type: ignore
        return None

    def extract_fingerprint(_obj):  # type: ignore
        class _FP:
            def to_dict(self):
                return {}

        return _FP()

    def verify_fingerprint(_obj):  # type: ignore
        return False


router = APIRouter(prefix="/v1/tee", tags=["security"])


@router.get("/status")
async def tee_status() -> dict[str, Any]:
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
