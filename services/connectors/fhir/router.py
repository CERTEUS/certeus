# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | FILE: services/connectors/fhir/router.py                            |
# | ROLE: FHIR connector (reason endpoint) — stub.                      |
# +=====================================================================+
from __future__ import annotations

from fastapi import APIRouter

router = APIRouter(prefix="/v1/connectors/fhir")


@router.post("/reason")
def reason(payload: dict) -> dict:
    return {"status": "PENDING", "plan": {"sources": ["FHIR"], "eta_s": 5}}
