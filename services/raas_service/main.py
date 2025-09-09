# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/raas_service/main.py                       |

# | ROLE: Project module.                                       |

# | PLIK: services/raas_service/main.py                       |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: RAaaS — Remote Attestation as a Service.
    Udostępnia dwa endpointy FastAPI:
      - GET /v1/ra/attestation — odczytaj aktualną attestację (z ENV/pliku)
      - POST /v1/ra/verify — zweryfikuj attestation i wyekstrahuj odcisk (RAFingerprint)

EN: RAaaS — Remote Attestation as a Service. Two FastAPI endpoints:
      - GET /v1/ra/attestation — read current attestation (ENV/file)
      - POST /v1/ra/verify — verify attestation and extract RAFingerprint
"""

from __future__ import annotations

from dataclasses import asdict
from typing import Any

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel, Field

from certeus.security.ra import (
    RAFingerprint,
    attestation_from_env,
    extract_fingerprint,
    verify_fingerprint,
)


class AttestationModel(BaseModel):
    # Opakowanie dowolnego JSONa attestation (dict)
    claims: dict[str, Any] = Field(default_factory=dict)


class FingerprintModel(BaseModel):
    vendor: str
    product: str
    measurement: str
    hwid: str | None = None


app = FastAPI(title="CERTEUS RAaaS", version="1.0.0")


@app.get("/v1/ra/attestation", response_model=AttestationModel)
def get_attestation() -> AttestationModel:
    att = attestation_from_env()
    if att is None:
        # Brak attestation — to nie jest błąd logiczny, ale dla RAaaS sygnalizujemy 404
        raise HTTPException(status_code=404, detail="No attestation available")
    # Normalizuj do pola claims dla spójności
    if "claims" in att and isinstance(att["claims"], dict):
        claims = att["claims"]
    else:
        claims = att
    return AttestationModel(claims=claims)


@app.post("/v1/ra/verify", response_model=FingerprintModel)
def post_verify(attestation: AttestationModel) -> FingerprintModel:
    fp: RAFingerprint = extract_fingerprint({"claims": attestation.claims})
    if not verify_fingerprint(asdict(fp)):
        raise HTTPException(status_code=400, detail="Invalid fingerprint")
    return FingerprintModel(**asdict(fp))


def main() -> int:  # pragma: no cover - launched via ASGI normally
    import uvicorn

    uvicorn.run(app, host="0.0.0.0", port=8091)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
