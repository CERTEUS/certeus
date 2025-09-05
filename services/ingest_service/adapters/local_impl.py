# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/adapters/local_impl.py      |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/adapters/local_impl.py      |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

# =============================================================================

#  CERTEUS — Local Adapters (stubs)

#  Preview/OCR/Drive/LLM — deterministic, no-cloud implementations

# =============================================================================

#  PL

#  Proste, lokalne implementacje interfejsów adapterów:

#   - LocalDriveAdapter: zapis/odczyt pod ./static

#   - StubPreviewAdapter: "DOCX→PDF" (1-str. PDF placeholder)

#   - StubOCRAdapter: zwraca 1 stronę z heurystycznym tekstem

#   - StubLLMAdapter: deterministyczny ALI-stub do /v1/analyze

#

#  EN

#  Simple local implementations of adapter interfaces:

#   - LocalDriveAdapter: save/read under ./static

#   - StubPreviewAdapter: "DOCX→PDF" (1-page PDF placeholder)

#   - StubOCRAdapter: returns 1 page with heuristic text

#   - StubLLMAdapter: deterministic ALI stub for /v1/analyze

#

#  Zasady/Rules:

#  - Deterministyczne ID: sha256(data, filename, content_type, case_id, salt)

#  - Tylko stdlib. Linie ≤ 100 znaków, LF, brak trailing spaces.

# =============================================================================

"""

PL: Lokalne implementacje stubów adapterów (bez chmury).

EN: Local stub implementations of adapters (no cloud).

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import asdict
import hashlib
from pathlib import Path

from .contracts import (
    DriveAdapter,
    DriveError,
    DriveSaveResult,
    LLMAdapter,
    LLMRequest,
    LLMResponse,
    OCRAdapter,
    OCRError,
    OCRPage,
    OCRRequest,
    PreviewAdapter,
    PreviewError,
    PreviewRequest,
    PreviewResult,
    infer_extension,
)

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class LocalDriveAdapter(DriveAdapter):
    """

    PL: Lokalny storage zapisujący do ./static; zwraca URL pod /static.

    EN: Local storage saving to ./static; returns URLs under /static.

    """

    def __init__(self, base_dir: str | Path = "static", base_url_prefix: str = "/static"):
        self.base_dir = Path(base_dir)

        self.base_url_prefix = base_url_prefix.rstrip("/")

    async def save_bytes(
        self,
        data: bytes,
        *,
        filename: str,
        content_type: str,
        case_id: str | None = None,
        deterministic: bool = True,
    ) -> DriveSaveResult:
        try:
            salt = "det" if deterministic else _stable_hexdigest(filename)

            file_id = _stable_hexdigest(data, filename, content_type, case_id or "", salt)

            ext = infer_extension(content_type)

            rel = Path("uploads") / (case_id or "general") / f"{file_id}{ext}"

            dst = self.base_dir / rel

            _ensure_dir(dst)

            dst.write_bytes(data)

            url = f"{self.base_url_prefix}/{rel.as_posix()}"

            return DriveSaveResult(
                file_id=str(rel),
                url=url,
                size_bytes=len(data),
                content_type=content_type,
                meta={"deterministic": deterministic},
            )

        except Exception as e:
            raise DriveError("LocalDriveAdapter.save_bytes failed") from e

    async def read_bytes(self, file_id: str) -> bytes:
        try:
            path = self.base_dir / Path(file_id)

            return path.read_bytes()

        except Exception as e:
            raise DriveError(f"LocalDriveAdapter.read_bytes failed: {file_id}") from e

    async def url_for(self, file_id: str) -> str | None:
        # PL: Dla lokalnego storage URL jest deterministyczny.

        # EN: Deterministic URL for local storage.

        rel = Path(file_id)

        return f"{self.base_url_prefix}/{rel.as_posix()}"


class StubPreviewAdapter(PreviewAdapter):
    """

    PL:

      Tworzy minimalny PDF (1 strona) jako placeholder podglądu.

      Nie wykonuje realnej konwersji DOCX→PDF; to most do UI (/v1/preview).

    EN:

      Produces a minimal PDF (1 page) as preview placeholder.

      No real DOCX→PDF; just a bridge to the UI (/v1/preview).

    """

    def __init__(self, drive: LocalDriveAdapter):
        self.drive = drive

    @staticmethod
    def _minimal_pdf(title: str) -> bytes:
        # PL: Mini-PDF wystarczający do smoke-testu w przeglądarce.

        # EN: Tiny PDF good enough for a browser smoke test.

        # Uwaga: nieidealny, ale poprawny syntaktycznie.

        pdf = (
            b"%PDF-1.4\n"
            b"1 0 obj<</Type/Catalog/Pages 2 0 R>>endobj\n"
            b"2 0 obj<</Type/Pages/Count 1/Kids[3 0 R]>>endobj\n"
            b"3 0 obj<</Type/Page/Parent 2 0 R/MediaBox[0 0 612 792]/Contents 4 0 R"
            b"/Resources<</Font<</F1 5 0 R>>>>>>endobj\n"
            b"4 0 obj<</Length 55>>stream\nBT\n/F1 24 Tf\n72 720 Td\n("
            + title.encode("latin-1", "ignore")
            + b") Tj\nET\nendstream\nendobj\n"
            b"5 0 obj<</Type/Font/Subtype/Type1/BaseFont/Helvetica>>endobj\n"
            b"xref\n0 6\n0000000000 65535 f \n"
            b"0000000010 00000 n \n0000000060 00000 n \n0000000116 00000 n \n"
            b"0000000276 00000 n \n0000000401 00000 n \n"
            b"trailer<</Size 6/Root 1 0 R>>\nstartxref\n480\n%%EOF\n"
        )

        return pdf

    async def generate(self, request: PreviewRequest) -> PreviewResult:
        try:
            title = f"Preview: {request.blob.filename}"

            pdf_bytes = self._minimal_pdf(title)

            saved = await self.drive.save_bytes(
                pdf_bytes,
                filename=request.blob.filename,
                content_type="application/pdf",
                case_id=request.case_id,
                deterministic=request.deterministic,
            )

            url = await self.drive.url_for(saved.file_id)

            return PreviewResult(
                url=url or "",
                content_type="application/pdf",
                pages=1,
                size_bytes=len(pdf_bytes),
                meta={
                    "source_content_type": request.blob.content_type,
                    "note": "stub preview",
                },
            )

        except Exception as e:
            raise PreviewError("StubPreviewAdapter.generate failed") from e


class StubOCRAdapter(OCRAdapter):
    """

    PL: Zwraca jedną stronę z prostym tekstem na podstawie metadanych pliku.

    EN: Returns single page with simple text based on file metadata.

    """

    async def extract(self, request: OCRRequest) -> Iterable[OCRPage]:
        try:
            text = (
                f"[STUB_OCR]\nfilename={request.blob.filename}\n"
                f"content_type={request.blob.content_type}\n"
                f"bytes={len(request.blob.data)}\nlang_hint={request.lang_hint}\n"
            )

            return [OCRPage(index=0, text=text, meta={"stub": True})]

        except Exception as e:
            raise OCRError("StubOCRAdapter.extract failed") from e


class StubLLMAdapter(LLMAdapter):
    """

    PL: Deterministyczny stub. Nie łączy się z żadnym LLM.

    EN: Deterministic stub. Does not call any LLM.

    """

    def __init__(self, model_name: str = "ALI-Stub-0"):
        self.model_name = model_name

    async def analyze(self, request: LLMRequest) -> LLMResponse:
        try:
            att_summary: list[str] = []

            for a in request.attachments:
                if isinstance(a.content, bytes | bytearray):
                    size = len(a.content)

                else:
                    size = len(str(a.content))

                att_summary.append(f"{a.kind}:{a.name}:{size}")

            answer = {
                "summary": {"prompt_len": len(request.prompt), "attachments": att_summary},
                "satisfied": [],
                "missing": [],
            }

            trace: Sequence[str] = ("stub:init", "stub:analyze", "stub:done")

            provenance = {
                "adapter": "StubLLMAdapter",
                "request": {**asdict(request), "attachments": None},
            }

            return LLMResponse(
                status="ok",
                model=self.model_name,
                answer=answer,
                trace=trace,
                provenance=provenance,
            )

        except Exception as e:
            raise DriveError("StubLLMAdapter.analyze failed") from e


# === LOGIKA / LOGIC ===

# ------------------------------ Helpers -------------------------------------


def _stable_hexdigest(*parts: str | bytes) -> str:
    """PL/EN: Deterministic short sha256 hex."""

    h = hashlib.sha256()

    for p in parts:
        if isinstance(p, str):
            p = p.encode("utf-8", "ignore")

        h.update(p)

    return h.hexdigest()[:24]


def _ensure_dir(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


# --------------------------- LocalDriveAdapter ------------------------------

# --------------------------- StubPreviewAdapter -----------------------------

# ----------------------------- StubOCRAdapter -------------------------------

# ----------------------------- StubLLMAdapter -------------------------------

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
