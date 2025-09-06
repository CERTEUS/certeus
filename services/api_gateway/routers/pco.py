# +-------------------------------------------------------------+
# |             CERTEUS - PCO / ProofBundle Router              |
# +-------------------------------------------------------------+
# | PLIK / FILE: services/api_gateway/routers/pco.py            |
# | ROLA / ROLE:                                                |
# |  PL: Endpointy do tworzenia i odczytu ProofBundle v0.2.     |
# |  EN: Endpoints for creating and reading ProofBundle v0.2.   |
# +-------------------------------------------------------------+

"""PL: API dla ProofBundle v0.2. EN: API for ProofBundle v0.2."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from fastapi import APIRouter, Body, HTTPException
from jsonschema import Draft202012Validator

# === KONFIGURACJA / CONFIGURATION ===

router = APIRouter(tags=["PCO"])

_SCHEMA_PATH = Path(__file__).resolve().parents[1] / "schemas" / "proofbundle_v0.2.json"
_PROOFBUNDLE_SCHEMA = json.loads(_SCHEMA_PATH.read_text(encoding="utf-8"))
_VALIDATOR = Draft202012Validator(_PROOFBUNDLE_SCHEMA)

# === LOGIKA / LOGIC ===


async def _create_and_sign_bundle(bundle_request: dict) -> dict:
    """Stub: Logika tworzenia, walidacji, podpisywania i zapisu do ledger."""
    # 1. Walidacja ze schematem
    errors = sorted(_VALIDATOR.iter_errors(bundle_request), key=lambda e: e.path)
    if errors:
        # Zwróć pierwszy błąd walidacji dla lepszego debugowania
        error_details = [
            f"Validation error at `{' -> '.join(map(str, e.path))}`: {e.message}"
            for e in errors
        ]
        raise HTTPException(
            status_code=422,  # Unprocessable Entity
            detail={"code": "validation_error", "errors": error_details},
        )

    # 2. Uruchomienie polityk z policy_pack.yaml (stub)
    # 3. Obliczenie metryk ryzyka (stub)
    # 4. Ustalenie finalnego statusu (stub)
    # 5. Podpisanie kluczem Ed25519 (stub)
    # 6. Zapis do PCO-Ledger (stub)
    # 7. Zwrócenie finalnego, podpisanego bundle

    # Mock: Ustawiamy status i wersję, jeśli ich nie ma
    bundle_request["status"] = "PUBLISH"  # MOCK
    bundle_request["version"] = "0.2"  # MOCK
    return bundle_request


# === I/O / ENDPOINTS ===


@router.post("/v1/pco/bundle", summary="Create and publish a ProofBundle")
async def create_proof_bundle(bundle_request: dict[str, Any] = Body(...)):  # noqa: B008
    """Tworzy, waliduje, podpisuje i publikuje ProofBundle v0.2."""
    signed_bundle = await _create_and_sign_bundle(bundle_request)
    return signed_bundle


@router.get("/pco/public/{case_id}", summary="Get public payload of a ProofBundle")
async def get_public_proof_bundle(case_id: str):
    """Zwraca publiczny (zredagowany) payload dla danego case_id."""
    # 1. Fetch from PCO-Ledger
    # 2. Ensure PII is redacted
    raise HTTPException(status_code=501, detail="Not Implemented")
