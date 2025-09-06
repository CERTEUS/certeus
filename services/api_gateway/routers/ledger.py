# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/ledger.py              |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/ledger.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Router FastAPI dla księgi pochodzenia (ledger):

    - /record-input       : rejestruje dokument wejściowy,

    - /{case_id}/records  : pobiera wpisy dla sprawy,

    - /{case_id}/prove    : buduje i (opcjonalnie) waliduje paragon pochodzenia.

EN: FastAPI router for the provenance ledger:

    - /record-input       : record an input document,

    - /{case_id}/records  : list entries for a case,

    - /{case_id}/prove    : build and (optionally) validate a provenance receipt.

"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any, Protocol, cast

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, Field

# Import the module, then obtain a working singleton/instance.
import services.ledger_service.ledger as ledger_mod  # noqa: F401

# --- Protocol to satisfy type checker (methods used by this router) ---


class LedgerLike(Protocol):
    def record_input(self, *, case_id: str, document_hash: str) -> dict[str, Any]: ...

    def get_records_for_case(self, *, case_id: str) -> list[dict[str, Any]]: ...

    def build_provenance_receipt(self, *, case_id: str) -> dict[str, Any]: ...


# Prefer existing singleton; else instantiate a fresh Ledger from the module.

ledger_service: LedgerLike = cast(
    LedgerLike,
    getattr(ledger_mod, "ledger_service", None) or ledger_mod.Ledger(),  # type: ignore[attr-defined, call-arg]
)

# Optional JSON Schema validation (soft dependency)

try:
    from jsonschema import Draft7Validator  # type: ignore

except Exception:  # pragma: no cover
    Draft7Validator = None  # type: ignore[assignment]

router = APIRouter(prefix="/v1/ledger")

# Repo paths

REPO_ROOT = Path(__file__).resolve().parents[3]

SCHEMAS_DIR = REPO_ROOT / "schemas"

# Lazy schema/validator (not hard constants)

_provenance_schema: dict[str, Any] | None = None

_provenance_validator: Any | None = None

if Draft7Validator is not None:
    schema_path = SCHEMAS_DIR / "provenance_receipt_v1.json"

    if schema_path.exists():
        try:
            _provenance_schema = json.loads(schema_path.read_text(encoding="utf-8"))

            _provenance_validator = Draft7Validator(_provenance_schema)  # type: ignore[call-arg]

        except Exception:
            _provenance_schema = None

            _provenance_validator = None

# === MODELS ===


class RecordInputRequest(BaseModel):
    """

    PL: Wejście do zarejestrowania dokumentu.

    EN: Input to record a document ingestion.

    """

    case_id: str = Field(..., min_length=1, description="PL: Id sprawy. / EN: Case identifier.")

    document_hash: str = Field(
        ...,
        min_length=7,
        description="PL: Np. 'sha256:<hex>'. / EN: e.g., 'sha256:<hex>'.",
    )


class RecordInputResponse(BaseModel):
    """

    PL: Odpowiedź na zarejestrowanie dokumentu.

    EN: Response for recorded document ingestion.

    """

    event_id: int

    type: str

    case_id: str

    document_hash: str | None

    timestamp: str

    chain_prev: str | None

    chain_self: str


# === ENDPOINTS ===


@router.post("/record-input", response_model=RecordInputResponse, tags=["Ledger"])
def record_input(payload: RecordInputRequest, request: Request) -> RecordInputResponse:
    """

    PL: Rejestruje nowy dokument w księdze (INPUT_INGESTION).

    EN: Records a new document in the ledger (INPUT_INGESTION).

    """

    # PNIP validation (strict mode optional)
    try:
        from services.api_gateway.pnip import validate_pnip_request

        strict = (os.getenv("STRICT_PNIP") or "0").strip() in {"1", "true", "True"}
        _ = validate_pnip_request(request, body=payload.model_dump(), strict=strict)
    except HTTPException as e:
        # Re-raise PNIP errors as-is (400 with PCO error)
        raise e
    except Exception:
        # Soft-fail PNIP in non-strict mode
        pass

    result = ledger_service.record_input(case_id=payload.case_id, document_hash=payload.document_hash)

    return RecordInputResponse(**result)


@router.get("/{case_id}", tags=["Ledger"])
def get_ledger_head(case_id: str) -> dict[str, Any]:
    """

    PL: Zwraca prosty „head” księgi dla sprawy (ostatnie ogniwo łańcucha) oraz długość.

    EN: Returns a simple ledger head for the case (last chain link) and length.

    """

    items = ledger_service.get_records_for_case(case_id=case_id)

    if not items:
        # Spójne z minimalnym kontraktem – brak definicji schematu w OpenAPI.
        return {"case_id": case_id, "length": 0, "head": None}

    head = items[-1]

    return {
        "case_id": case_id,
        "length": len(items),
        "head": head.get("chain_self"),
        "type": head.get("type"),
        "timestamp": head.get("timestamp"),
    }


@router.get("/{case_id}/records", tags=["Ledger"])
def get_records(case_id: str) -> list[RecordInputResponse]:
    """

    PL: Zwraca listę wpisów dla danego case_id.

    EN: Returns all entries for the given case_id.

    """

    items = ledger_service.get_records_for_case(case_id=case_id)

    return [RecordInputResponse(**it) for it in items]


@router.get("/{case_id}/prove", tags=["Ledger"])
def prove_case(case_id: str) -> dict[str, Any]:
    """

    PL: Generuje i (jeśli możliwe) waliduje Provenance Receipt dla sprawy.

    EN: Generates and (if available) validates the Provenance Receipt for a case.

    """

    try:
        receipt = ledger_service.build_provenance_receipt(case_id=case_id)

    except ValueError as e:
        raise HTTPException(status_code=404, detail=str(e)) from e

    # Optional schema validation (enable with LEDGER_VALIDATE_SCHEMA=1)

    if os.getenv("LEDGER_VALIDATE_SCHEMA") == "1" and _provenance_validator is not None:
        try:
            _provenance_validator.validate(receipt)  # type: ignore[union-attr]

        except Exception as e:
            # 500: service error (receipt doesn't match contract)

            raise HTTPException(
                status_code=500,
                detail=f"Provenance receipt schema validation failed: {e}",
            ) from e

    return receipt
