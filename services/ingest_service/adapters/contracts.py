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

# === IMPORTY / IMPORTS ===`nfrom __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Protocol


# === MODELE / MODELS ===
@dataclass(slots=True)
class Blob:
    """PL/EN: Surowe dane pliku (nazwa, MIME, bajty)."""

    filename: str
    content_type: str
    data: bytes


@dataclass(slots=True)
class PreviewRequest:
    """PL/EN: Wejście do adaptera preview (blob, case_id, format docelowy)."""

    blob: Blob
    case_id: str
    target_format: str = "application/pdf"
    deterministic: bool = True


@dataclass(slots=True)
class PreviewResult:
    file_id: str
    url: str | None
    size_bytes: int
    content_type: str
    meta: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class OCRPage:
    index: int
    text: str
    meta: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class OCRRequest:
    blob: Blob
    case_id: str | None = None
    lang_hint: str | None = None


@dataclass(slots=True)
class DriveSaveResult:
    file_id: str
    url: str | None
    size_bytes: int
    content_type: str
    meta: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class LLMRequest:
    prompt: str
    attachments: Sequence[Blob] | None = None
    params: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class LLMResponse:
    model: str
    answer: str
    trace: list[str] = field(default_factory=list)
    metrics: dict[str, Any] = field(default_factory=dict)


# === WYJĄTKI / ERRORS ===
class AdapterError(Exception):
    """Base class for adapter errors."""


class PreviewError(AdapterError):
    pass


class OCRError(AdapterError):
    pass


class DriveError(AdapterError):
    pass


class LLMError(AdapterError):
    pass


# === INTERFEJSY / PROTOCOLS ===
class PreviewAdapter(Protocol):
    async def generate(self, request: PreviewRequest) -> PreviewResult: ...


class OCRAdapter(Protocol):
    async def extract(self, request: OCRRequest) -> Iterable[OCRPage]: ...


class DriveAdapter(Protocol):
    async def save_bytes(
        self,
        data: bytes,
        *,
        filename: str,
        content_type: str,
        case_id: str | None = None,
        deterministic: bool = True,
    ) -> DriveSaveResult: ...

    async def read_bytes(self, file_id: str) -> bytes: ...

    async def url_for(self, file_id: str) -> str | None: ...


class LLMAdapter(Protocol):
    async def analyze(self, request: LLMRequest) -> LLMResponse: ...`n# ----------------------------- Common DTOs ----------------------------------`n# ----------------------------- Common DTOs ----------------------------------


@dataclass(slots=True)


@dataclass(slots=True)


@dataclass


@dataclass


@dataclass


@dataclass


@dataclass


@dataclass


@dataclass






















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


