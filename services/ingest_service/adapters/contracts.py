# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/adapters/contracts.py       |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/adapters/contracts.py       |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# =============================================================================

#  CERTEUS — Adapters Contracts

#  Preview/OCR/Drive/LLM interfaces (Protocols) + lightweight DTOs

# =============================================================================

#  PL

#  Ten moduł definiuje kontrakty (interfejsy) adapterów używanych przez API:

#  - PreviewAdapter: DOCX→PDF (i ogólny preview), zwraca PreviewResult

#  - OCRAdapter: ekstrakcja tekstu z PDF/obrazów (stub na start)

#  - DriveAdapter: prosty storage (np. lokalny /static albo chmura)

#  - LLMAdapter: analiza/inspekcja treści (stub ALI pod /v1/analyze)

#

#  Zasady:

#  - Proste DTO z dataclasses (bez zależności pydantic).

#  - Asynchroniczne metody (spójne z FastAPI).

#  - Linie do 100 znaków, LF, brak trailing whitespace.

#  - Wyjątki dziedziczą po AdapterError.

#

#  EN

#  This module defines adapter contracts used by the API layer:

#  - PreviewAdapter: DOCX→PDF (generic preview), returns PreviewResult

#  - OCRAdapter: text extraction from PDFs/images (stub initially)

#  - DriveAdapter: storage abstraction (local /static or cloud)

#  - LLMAdapter: analysis/inspection (ALI stub used by /v1/analyze)

#

#  Rules:

#  - Lightweight DTOs via dataclasses (no pydantic dependency).

#  - Async methods (compatible with FastAPI).

#  - 100-char lines, LF endings, no trailing whitespace.

#  - Exceptions derive from AdapterError.

# =============================================================================

"""

PL: Kontrakty adapterów i lekkie DTO (Preview/OCR/Drive/LLM) używane przez API.

EN: Adapter contracts and lightweight DTOs (Preview/OCR/Drive/LLM) used by the API.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Literal, Protocol

# ----------------------------- Common DTOs ----------------------------------


@dataclass(slots=True)
class Blob:
    """

    PL: Surowe dane pliku.

    EN: Raw file payload.

    """

    filename: str

    content_type: str

    data: bytes


@dataclass(slots=True)
class PreviewRequest:
    """

    PL: Wejście do adaptera preview. 'target_format' np. 'application/pdf'.

    EN: Input for preview adapter. 'target_format' e.g. 'application/pdf'.

    """

    blob: Blob

    case_id: str

    target_format: str = "application/pdf"

    deterministic: bool = True


@dataclass
class PreviewResult:
    """

    PL: Wynik generowania podglądu. 'url' wskazuje zasób serwowany przez API.

    EN: Preview generation result. 'url' points to API-served resource.

    """

    url: str

    content_type: str

    pages: int | None = None

    size_bytes: int | None = None

    meta: Mapping[str, Any] = field(default_factory=dict)


@dataclass
class OCRPage:
    """

    PL: Tekst i proste metadane strony po OCR.

    EN: OCR'ed page text and basic metadata.

    """

    index: int

    text: str

    width_px: int | None = None

    height_px: int | None = None

    meta: Mapping[str, Any] = field(default_factory=dict)


@dataclass
class OCRRequest:
    """

    PL: Wejście do OCR; jeśli PDF → stronicowanie wewnątrz adaptera.

    EN: OCR input; if PDF → paging handled inside the adapter.

    """

    blob: Blob

    lang_hint: str = "pl+en"

    dpi: int = 300

    max_pages: int | None = None

    case_id: str | None = None


@dataclass
class DriveSaveResult:
    """

    PL: Wynik zapisu do storage (lokalny/chmura).

    EN: Storage save result (local/cloud).

    """

    file_id: str

    url: str | None = None

    size_bytes: int | None = None

    content_type: str | None = None

    meta: Mapping[str, Any] = field(default_factory=dict)


@dataclass
class Attachment:
    """

    PL: Załącznik do analizy LLM (np. tekst OCR).

    EN: Attachment for LLM analysis (e.g., OCR text).

    """

    name: str

    kind: Literal["text", "preview_url", "binary"]

    content: str | bytes

    content_type: str | None = None


@dataclass
class LLMRequest:
    """

    PL: Wejście do adaptera LLM.

    EN: Input for LLM adapter.

    """

    prompt: str

    attachments: Sequence[Attachment] = ()

    case_id: str | None = None

    model_hint: str | None = None

    temperature: float = 0.0

    max_tokens: int | None = None


@dataclass
class LLMResponse:
    """

    PL: Zunifikowany wynik LLM do /v1/analyze (stub ALI).

    EN: Unified LLM result for /v1/analyze (ALI stub).

    """

    status: Literal["ok", "error"]

    model: str

    answer: Mapping[str, Any]

    trace: Sequence[str] = ()

    provenance: Mapping[str, Any] = field(default_factory=dict)

    error: str | None = None


class AdapterError(RuntimeError):
    """PL: Błąd ogólny adapterów. EN: Generic adapters error."""


class PreviewError(AdapterError):
    """PL/EN: Preview adapter error."""


class OCRError(AdapterError):
    """PL/EN: OCR adapter error."""


class DriveError(AdapterError):
    """PL/EN: Drive/storage adapter error."""


class LLMError(AdapterError):
    """PL/EN: LLM adapter error."""


class PreviewAdapter(Protocol):
    """

    PL:

      Interfejs generowania podglądu (np. DOCX→PDF).

      Kontrakt:

        - Wejście: PreviewRequest

        - Wyjście: PreviewResult (URL serwowany przez API, np. /static/previews/..)

        - Determinizm: dla tych samych danych i case_id ścieżka może być stała.

    EN:

      Preview generation interface (e.g., DOCX→PDF).

      Contract:

        - Input: PreviewRequest

        - Output: PreviewResult (API-served URL, e.g., /static/previews/..)

        - Determinism: stable path for same input + case_id (optional).

    """

    async def generate(self, request: PreviewRequest) -> PreviewResult:
        """PL/EN: Produce preview for given blob."""

        ...


class OCRAdapter(Protocol):
    """

    PL:

      Interfejs OCR dla PDF/obrazów.

      Kontrakt:

        - Wejście: OCRRequest

        - Wyjście: Iterable[OCRPage] (kolejność stron gwarantowana)

        - Minimalna gwarancja stubu: zwróć 1 stronę z prostym 'text' (echo/heurystyka)

    EN:

      OCR interface for PDF/images.

      Contract:

        - Input: OCRRequest

        - Output: Iterable[OCRPage] (page order guaranteed)

        - Stub minimum guarantee: return 1 page with basic 'text' (echo/heuristic)

    """

    async def extract(self, request: OCRRequest) -> Iterable[OCRPage]:
        """PL/EN: Extract text pages from the blob (PDF/image)."""

        ...


class DriveAdapter(Protocol):
    """

    PL:

      Abstrakcja storage (lokalny katalog /static, S3, GDrive, itd.).

      Kontrakt:

        - save_bytes: zapisuje dane i zwraca logiczne ID oraz (opcjonalnie) URL

        - read_bytes: pobiera blob po file_id

        - url_for: zwraca publiczny URL jeśli dostępny

    EN:

      Storage abstraction (local /static, S3, GDrive, etc.).

      Contract:

        - save_bytes: persists payload and returns logical ID and optional URL

        - read_bytes: fetches payload by file_id

        - url_for: returns public URL if available

    """

    async def save_bytes(
        self,
        data: bytes,
        *,
        filename: str,
        content_type: str,
        case_id: str | None = None,
        deterministic: bool = True,
    ) -> DriveSaveResult:
        """PL/EN: Persist a payload and return its handle."""

        ...

    async def read_bytes(self, file_id: str) -> bytes:
        """PL/EN: Retrieve raw bytes by logical file id."""

        ...

    async def url_for(self, file_id: str) -> str | None:
        """PL/EN: Optional public URL for given file id."""

        ...


class LLMAdapter(Protocol):
    """

    PL:

      Interfejs do warstwy analitycznej LLM (stub ALI).

      Kontrakt:

        - analyze: zwraca LLMResponse zgodny z oczekiwaniem /v1/analyze

        - Implementacja stub: deterministyczny 'model', krótki 'trace', 'answer'

    EN:

      Interface to LLM analytical layer (ALI stub).

      Contract:

        - analyze: returns LLMResponse aligned with /v1/analyze expectations

        - Stub impl: deterministic 'model', short 'trace', 'answer'

    """

    async def analyze(self, request: LLMRequest) -> LLMResponse:
        """PL/EN: Perform analysis over prompt + attachments."""

        ...


# === LOGIKA / LOGIC ===


def infer_extension(content_type: str, fallback: str = ".bin") -> str:
    """

    PL: Prosty mapping MIME→rozszerzenie dla ścieżek deterministycznych.

    EN: Simple MIME→extension mapping for deterministic paths.

    """

    mapping = {
        "application/pdf": ".pdf",
        "application/vnd.openxmlformats-officedocument.wordprocessingml.document": ".docx",
        "text/plain": ".txt",
        "image/png": ".png",
        "image/jpeg": ".jpg",
        "image/jpg": ".jpg",
    }

    return mapping.get(content_type.lower(), fallback)


__all__ = [
    "Blob",
    "PreviewRequest",
    "PreviewResult",
    "OCRPage",
    "OCRRequest",
    "DriveSaveResult",
    "Attachment",
    "LLMRequest",
    "LLMResponse",
    "AdapterError",
    "PreviewError",
    "OCRError",
    "DriveError",
    "LLMError",
    "PreviewAdapter",
    "OCRAdapter",
    "DriveAdapter",
    "LLMAdapter",
    "infer_extension",
]


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
