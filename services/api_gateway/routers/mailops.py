#!/usr/bin/env python3
"""
PL: Router FastAPI dla obszaru MailOps ingest/headers.

EN: FastAPI router for MailOps ingest/headers.
"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===


#!/usr/bin/env python3


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/mailops.py                       |

# | ROLE: MailOps ingest + normalize                                    |

# +=====================================================================+

from __future__ import annotations

from fastapi import APIRouter, Request
from pydantic import BaseModel, Field

router = APIRouter(prefix="/v1/mailops", tags=["MailOps"])


class Attachment(BaseModel):
    filename: str

    content_type: str | None = None

    size: int = 0


class IngestEmailRequest(BaseModel):
    mail_id: str

    thread_id: str | None = None

    from_addr: str

    to: list[str]

    subject: str | None = None

    body_text: str | None = None

    spf: str | None = None

    dkim: str | None = None

    dmarc: str | None = None

    attachments: list[Attachment] = Field(default_factory=list)


class IngestEmailResponse(BaseModel):
    ok: bool

    io: dict


@router.post("/ingest", response_model=IngestEmailResponse)
async def ingest_email(req: IngestEmailRequest, request: Request) -> IngestEmailResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    # Normalize into io.email.* fields

    io_email = {
        "io.email.mail_id": req.mail_id,
        "io.email.thread_id": req.thread_id,
        "io.email.spf": req.spf,
        "io.email.dkim": req.dkim,
        "io.email.dmarc": req.dmarc,
        "attachments": [a.model_dump() for a in req.attachments],
    }

    return IngestEmailResponse(ok=True, io=io_email)
