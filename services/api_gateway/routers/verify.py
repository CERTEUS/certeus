# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/verify.py              |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/verify.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Publiczny endpoint do weryfikacji formuł SMT-LIB2 przez Silnik Prawdy.

EN: Public endpoint to verify SMT-LIB2 formulas via the Truth Engine.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel

from kernel.mismatch_protocol import MismatchError
from kernel.truth_engine import DualCoreVerifier

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

class VerificationRequest(BaseModel):
    """

    PL: Wejściowy DTO do weryfikacji (MVP: tylko 'smt2').

    EN: Input DTO for verification (MVP: 'smt2' only).

    """

    formula: str

    lang: str = "smt2"

# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1", tags=["Truth Engine"])

_verifier = DualCoreVerifier()

# === I/O / ENDPOINTS ===

@router.post("/verify")
def verify_formula(req: VerificationRequest) -> dict[str, Any]:
    """

    PL: Weryfikuje formułę. Zwraca sat/unsat/unknown oraz artefakty (model/proof).

    EN: Verifies the formula. Returns sat/unsat/unknown and artifacts (model/proof).

    """

    try:
        # lang w DualCoreVerifier.verify jest parametrem *keyword-only*.

        return _verifier.verify(req.formula, lang=req.lang)

    except MismatchError as e:
        raise HTTPException(
            status_code=409,
            detail={"requires_human": True, "message": str(e)},
        ) from e

    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e)) from e

    except Exception as e:  # pragma: no cover
        raise HTTPException(status_code=500, detail=f"Unexpected error: {e}") from e

# === TESTY / TESTS ===
