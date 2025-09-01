# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/test_adapters_local_impl.py                   |

# | ROLE: Project module.                                       |

# | PLIK: tests/test_adapters_local_impl.py                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# =============================================================================

#  Tests — Local Adapters stubs

# =============================================================================

#!/usr/bin/env python3

"""

PL: Testy minimalnych, lokalnych implementacji adapterów.

EN: Tests for minimal, local adapter implementations.

"""

from __future__ import annotations

from pathlib import Path

import pytest

from services.ingest_service.adapters.contracts import (
    Attachment,
    Blob,
    LLMRequest,
    OCRRequest,
    PreviewRequest,
)
from services.ingest_service.adapters.local_impl import (
    LocalDriveAdapter,
    StubLLMAdapter,
    StubOCRAdapter,
    StubPreviewAdapter,
)


@pytest.mark.asyncio
async def test_drive_roundtrip(tmp_path: Path) -> None:
    drive = LocalDriveAdapter(base_dir=tmp_path / "static", base_url_prefix="/static")

    data = b"hello"

    saved = await drive.save_bytes(data, filename="x.txt", content_type="text/plain", case_id="caseA")

    assert saved.file_id.endswith(".txt")

    raw = await drive.read_bytes(saved.file_id)

    assert raw == data

    url = await drive.url_for(saved.file_id)

    assert url and url.startswith("/static/")


@pytest.mark.asyncio
async def test_preview_stub_docx_to_pdf(tmp_path: Path) -> None:
    drive = LocalDriveAdapter(base_dir=tmp_path / "static", base_url_prefix="/static")

    preview = StubPreviewAdapter(drive)

    blob = Blob(
        filename="sample.docx",
        content_type=("application/vnd.openxmlformats-officedocument.wordprocessingml.document"),
        data=b"DOCX_BYTES_STUB",
    )

    req = PreviewRequest(blob=blob, case_id="caseB", target_format="application/pdf")

    res1 = await preview.generate(req)

    res2 = await preview.generate(req)

    assert res1.content_type == "application/pdf"

    assert res1.url.startswith("/static/")

    # Deterministic URL (same inputs):

    assert res1.url == res2.url

    # File exists:

    path_rel = res1.url.removeprefix("/static/")

    assert (tmp_path / "static" / path_rel).exists()


@pytest.mark.asyncio
async def test_ocr_stub_returns_page() -> None:
    ocr = StubOCRAdapter()

    blob = Blob(filename="scan.png", content_type="image/png", data=b"\x89PNG...")

    pages = await ocr.extract(OCRRequest(blob=blob, lang_hint="pl+en"))

    pages = list(pages)

    assert len(pages) >= 1

    assert pages[0].index == 0

    assert "filename=scan.png" in pages[0].text


@pytest.mark.asyncio
async def test_llm_stub_deterministic() -> None:
    llm = StubLLMAdapter()

    req = LLMRequest(
        prompt="Check attachments.",
        attachments=[
            Attachment(name="a.txt", kind="text", content="ABC"),
            Attachment(name="p.pdf", kind="preview_url", content="/static/x.pdf"),
        ],
        case_id="caseC",
    )

    res = await llm.analyze(req)

    assert res.status == "ok"

    assert res.model.startswith("ALI-Stub")

    assert "attachments" in res.answer["summary"]

    assert isinstance(res.trace, tuple)
