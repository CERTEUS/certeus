# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/api_gateway/routers/verify.py  |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/verify.py                |
# | ROLE: Expose /v1/verify endpoint (Truth Engine).            |
# | PLIK: services/api_gateway/routers/verify.py                |
# | ROLA: Udostępnia endpoint /v1/verify (Silnik Prawdy).       |
# +-------------------------------------------------------------+
"""
PL: Publiczny endpoint do weryfikacji formuł SMT-LIB2 przez Silnik Prawdy.
EN: Public endpoint to verify SMT-LIB2 formulas via the Truth Engine.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ======================================== #
from typing import Any, Dict
from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
from kernel.truth_engine import DualCoreVerifier
from kernel.mismatch_protocol import MismatchError

# === ROUTER / ROUTER ========================================== #
router = APIRouter(prefix="/v1", tags=["Truth Engine"])
_verifier = DualCoreVerifier()


# === DTO / MODELE DANYCH ====================================== #
class VerificationRequest(BaseModel):
    """
    PL: Wejściowy DTO do weryfikacji (MVP: tylko 'smt2').
    EN: Input DTO for verification (MVP: 'smt2' only).
    """

    formula: str
    lang: str = "smt2"


# === ENDPOINTY / ENDPOINTS ==================================== #
@router.post("/verify")
def verify_formula(req: VerificationRequest) -> Dict[str, Any]:
    """
    PL: Weryfikuje formułę. Zwraca sat/unsat/unknown oraz artefakty (model/proof).
    EN: Verifies the formula. Returns sat/unsat/unknown and artifacts (model/proof).
    """
    try:
        # lang w DualCoreVerifier.verify jest parametrem *keyword-only*.
        return _verifier.verify(req.formula, lang=req.lang)
    except MismatchError as e:
        # Rozjazd sędziów: konflikt 409 z flagą requires_human
        raise HTTPException(
            status_code=409, detail={"requires_human": True, "message": str(e)}
        )
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:  # pragma: no cover
        raise HTTPException(status_code=500, detail=f"Unexpected error: {e}")
