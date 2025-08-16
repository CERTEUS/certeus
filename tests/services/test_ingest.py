# +-------------------------------------------------------------+
# |                        CERTEUS                              |
# |        Core Engine for Reliable & Unified Systems           |
# +-------------------------------------------------------------+
# ── CERTEUS Project ─────────────────────────────────────────────────────────────
# File: tests/services/test_ingest.py
# License: Apache-2.0
# Description (PL): Testy integracyjne endpointu /v1/ingest (OCR→FACTLOG).
# Description (EN): Integration tests for /v1/ingest endpoint (OCR→FACTLOG).
# Style Guide: PL/EN docs, labeled blocks, strict asserts.
# ────────────────────────────────────────────────────────────────

"""
PL: Ten moduł testuje ścieżkę sukcesu i błędy (415, 413) dla /v1/ingest.
EN: This module tests the success path and errors (415, 413) for /v1/ingest.
"""

# [BLOCK: IMPORTS]
from fastapi.testclient import TestClient
from services.api_gateway.main import app
from typing import List, TypedDict, NotRequired, cast

import io


# [BLOCK: TYPES]
class FactJSON(TypedDict):
    """PL/EN: Minimal JSON schema of Fact used in tests (runtime-validated by API)."""

    fact_id: str
    role: str
    schema_version: str
    thesis: str
    source_document_hash: str
    confidence_score: float
    source_page: NotRequired[int]
    event_date: NotRequired[str]


# [BLOCK: CLIENT]
client = TestClient(app)


# [BLOCK: TEST – SUCCESS PATH]
def test_ingest_success_returns_two_facts():
    mock_bytes = b"%PDF-1.4 dummy"
    r = client.post(
        "/v1/ingest",
        files={"file": ("test.pdf", io.BytesIO(mock_bytes), "application/pdf")},
    )
    assert r.status_code == 200, r.text
    data: List[FactJSON] = cast(List[FactJSON], r.json())
    roles: set[str] = {item["role"] for item in data}
    assert roles == {
        "claim_contract_date",
        "evidence_payment",
    }  # użycie zmiennej → koniec F841
    for f in data:
        assert f["source_document_hash"].startswith("sha256:")
        assert 0.0 <= f["confidence_score"] <= 1.0


# [BLOCK: TEST – 415]
def test_ingest_unsupported_media_type():
    r = client.post(
        "/v1/ingest",
        files={"file": ("x.exe", io.BytesIO(b"x"), "application/x-msdownload")},
    )
    assert r.status_code == 415


# [BLOCK: TEST – 413]
def test_ingest_too_large_file():
    big = io.BytesIO(b"0" * (10 * 1024 * 1024 + 1))  # 10MB + 1 byte
    r = client.post("/v1/ingest", files={"file": ("big.pdf", big, "application/pdf")})
    assert r.status_code == 413
