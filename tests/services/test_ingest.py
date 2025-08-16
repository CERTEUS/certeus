# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# | Core Engine for Reliable & Unified Systems                  |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_ingest.py                         |
# | ROLE: Integration tests for /v1/ingest endpoint.            |
# | PLIK: tests/services/test_ingest.py                         |
# | ROLA: Testy integracyjne endpointu /v1/ingest.              |
# +-------------------------------------------------------------+

"""
PL: Testy sprawdzają ścieżkę sukcesu (OCR stub → FACTLOG), nagłówek łańcucha
    Ledger oraz walidacje MIME i limit rozmiaru.
EN: Tests cover the success path (OCR stub → FACTLOG), the Ledger chain header,
    and MIME/size validations.
"""

# [BLOCK: IMPORTS]
from __future__ import annotations

import io
from typing import Any, IO, Dict, List, Set, Tuple, Literal, cast

from fastapi import FastAPI
from fastapi.testclient import TestClient

# Import jako moduł, a typ nadamy przez cast — to ucisza Pylance.
import services.api_gateway.main as api_main

# [BLOCK: CLIENT]
fastapi_app_typed: FastAPI = cast(FastAPI, api_main.app)  # type: ignore[attr-defined]
client: TestClient = TestClient(fastapi_app_typed)

# [BLOCK: TYPES]
# (filename, fileobj, mimetype)
FileTuple = Tuple[str, IO[bytes], str]

LEDGER_HEADER: Literal["X-CERTEUS-Ledger-Chain"] = "X-CERTEUS-Ledger-Chain"


def make_file(filename: str, content: bytes, mimetype: str) -> FileTuple:
    """
    PL: Zwraca krotkę pliku akceptowaną przez TestClient (multipart/form-data).
    EN: Returns a file tuple accepted by TestClient (multipart/form-data).
    """
    fileobj: IO[bytes] = io.BytesIO(content)
    return (filename, fileobj, mimetype)


# [BLOCK: TEST • SUCCESS PATH]
def test_ingest_document_endpoint_success() -> None:
    """
    PL: Wysyła mały „PDF” i oczekuje listy 2 faktów oraz poprawnego nagłówka Ledger.
    EN: Sends a small “PDF” and expects 2 facts and a valid Ledger header.
    """
    files: Dict[str, FileTuple] = {
        "file": make_file("test.pdf", b"%PDF-1.4 dummy", "application/pdf")
    }

    resp = client.post("/v1/ingest", files=files)
    assert resp.status_code == 200

    data_json: List[Dict[str, Any]] = cast(List[Dict[str, Any]], resp.json())
    assert isinstance(data_json, list)
    assert len(data_json) == 2

    # roles set
    roles: Set[str] = {entry["role"] for entry in data_json}
    assert roles == {"claim_contract_date", "evidence_payment"}

    # structure spot-check
    first: Dict[str, Any] = data_json[0]
    assert "fact_id" in first and isinstance(first["fact_id"], str)
    assert "thesis" in first and isinstance(first["thesis"], str)
    assert "confidence_score" in first and isinstance(
        first["confidence_score"], (int, float)
    )

    # ledger header
    assert LEDGER_HEADER in resp.headers
    chain = resp.headers[LEDGER_HEADER]
    assert chain  # non-empty
    parts: List[str] = chain.split(";")
    assert all(p.startswith("sha256:") for p in parts)


# [BLOCK: TEST • MIME VALIDATION]
def test_ingest_rejects_unsupported_mime() -> None:
    """
    PL: MIME spoza białej listy → 415.
    EN: MIME outside the allowlist → 415.
    """
    files_bad: Dict[str, FileTuple] = {
        "file": make_file("x.exe", b"MZ...", "application/x-msdownload")
    }
    resp = client.post("/v1/ingest", files=files_bad)
    assert resp.status_code == 415


# [BLOCK: TEST • SIZE LIMIT]
def test_ingest_rejects_too_large() -> None:
    """
    PL: Plik większy niż 10 MiB → 413.
    EN: File larger than 10 MiB → 413.
    """
    # API uses MAX_BYTES = 10 * 1024 * 1024; send +1 byte
    big: bytes = b"0" * (10 * 1024 * 1024 + 1)
    files_big: Dict[str, FileTuple] = {
        "file": make_file("big.pdf", big, "application/pdf")
    }
    resp = client.post("/v1/ingest", files=files_big)
    assert resp.status_code == 413
