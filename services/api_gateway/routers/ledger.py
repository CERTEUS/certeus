# +-------------------------------------------------------------+
# |                     CERTEUS - Ledger API                    |
# +-------------------------------------------------------------+
# | PLIK / FILE: services/api_gateway/routers/ledger.py         |
# | ROLA / ROLE: Router FastAPI dla operacji na księdze.        |
# |              FastAPI router for ledger operations.          |
# +-------------------------------------------------------------+

from __future__ import annotations

from typing import Any, Annotated

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field, StringConstraints

from services.ledger_service.ledger import ledger_service

router = APIRouter()


# === MODELE WEJ./WYJ. / IO MODELS ===
class RecordInputRequest(BaseModel):
    """
    PL: Wejście do rejestracji nowego dokumentu w księdze.
    EN: Input payload to record a new document in the ledger.
    """
    # Pydantic v2: ograniczenia przez StringConstraints w Annotated
    case_id: Annotated[
        str,
        StringConstraints(min_length=1, strip_whitespace=True),
        Field(description="PL: Id sprawy. / EN: Case identifier.")
    ]
    document_hash: Annotated[
        str,
        # np. 'sha256:<64-hex>' — możesz zaostrzyć/rozluźnić pattern wedle potrzeb
        StringConstraints(pattern=r"^sha256:[A-Fa-f0-9]{64}$", strip_whitespace=True),
        Field(description="PL: Np. 'sha256:<hex64>'. / EN: e.g. 'sha256:<hex64>'.")
    ]


class LedgerRecord(BaseModel):
    """
    PL: Pojedynczy zapis księgi.
    EN: Single ledger record.
    """
    event_id: int
    type: str
    case_id: str
    document_hash: str
    timestamp: str
    chain_prev: str | None = None
    chain_self: str


@router.post("/record-input", response_model=LedgerRecord)
def api_record_input(payload: RecordInputRequest) -> dict[str, Any]:
    """
    PL: Zarejestruj przyjęcie dokumentu w księdze.
    EN: Record document ingestion in the ledger.
    """
    # Pylance-clean: typy to już zwykłe 'str' — bez cast(...)
    try:
        entry = ledger_service.record_input(
            case_id=payload.case_id,
            document_hash=payload.document_hash,
        )
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e)) from e
    return entry


@router.get("/{case_id}/records", response_model=list[LedgerRecord])
def api_get_case_records(case_id: str) -> list[dict[str, Any]]:
    """
    PL: Pobierz wszystkie zapisy dla podanej sprawy.
    EN: Fetch all records for the given case.
    """
    return ledger_service.get_records_for_case(case_id=case_id)
