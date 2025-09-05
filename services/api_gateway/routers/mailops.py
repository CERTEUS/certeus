#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/mailops.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/mailops.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla obszaru MailOps ingest/headers.

EN: FastAPI router for MailOps ingest/headers.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os

from fastapi import APIRouter, Request
from pydantic import BaseModel, Field

from core.pfs.materialize import materialize_mail_attachment
from core.pfs.uri import mail_attachment_uri

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

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

# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/mailops.py                       |

# | ROLE: MailOps ingest + normalize                                    |

# +=====================================================================+

router = APIRouter(prefix="/v1/mailops", tags=["MailOps"])

@router.post("/ingest", response_model=IngestEmailResponse)
async def ingest_email(req: IngestEmailRequest, request: Request) -> IngestEmailResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    # Normalize into io.email.* fields

    # Build attachments with ProofFS URIs
    atts = [
        {
            **a.model_dump(),
            "pfs_uri": mail_attachment_uri(req.mail_id, a.filename),
        }
        for a in req.attachments
    ]

    io_email = {
        "io.email.mail_id": req.mail_id,
        "io.email.thread_id": req.thread_id,
        "io.email.spf": req.spf,
        "io.email.dkim": req.dkim,
        "io.email.dmarc": req.dmarc,
        "attachments": atts,
    }
    # Optional: materialize ProofFS artifacts for attachments (dev/test)
    flag = (os.getenv("PROOFS_FS_MATERIALIZE") or "").strip() in {"1", "true", "True"}
    if flag:
        for a in req.attachments:
            try:
                materialize_mail_attachment(
                    mail_id=req.mail_id,
                    filename=a.filename,
                    meta={
                        "content_type": a.content_type,
                        "declared_size": a.size,
                    },
                )
            except Exception:
                # Best-effort in dev/test; ignore write errors
                pass
    # Record to Ledger as an input (io.email.* hash)
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        doc_hash = "sha256:" + compute_provenance_hash(io_email, include_timestamp=False)
        case_id = req.thread_id or req.mail_id
        ledger_service.record_input(case_id=case_id or "mail-case", document_hash=doc_hash)
    except Exception:
        pass

    return IngestEmailResponse(ok=True, io=io_email)

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
