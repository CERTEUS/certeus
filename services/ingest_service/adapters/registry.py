# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/adapters/registry.py        |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/adapters/registry.py        |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# =============================================================================

#  CERTEUS — Adapters Registry (lazy singletons)

#  PL: Prosty rejestr adapterów (Preview/OCR/Drive/LLM) z leniwą inicjalizacją.

#  EN: Simple adapters registry (Preview/OCR/Drive/LLM) with lazy initialization.

# =============================================================================

#  Zasady / Rules:

#  - Brak zależności zewnętrznych; tylko stdlib.

#  - Linie ≤ 100 znaków, LF, brak trailing spaces.

#  - PL/EN docstringi, baner ASCII.

# =============================================================================

"""

PL: Rejestr adapterów (lazy singletons) — bez efektów ubocznych.

EN: Adapters registry (lazy singletons) — side-effect free.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path

from typing import cast

from .contracts import (
    DriveAdapter,
    LLMAdapter,
    OCRAdapter,
    PreviewAdapter,
)

from .local_impl import (
    LocalDriveAdapter,
    StubLLMAdapter,
    StubOCRAdapter,
    StubPreviewAdapter,
)

# === KONFIGURACJA / CONFIGURATION ===
_DRIVE: DriveAdapter | None = None

_PREVIEW: PreviewAdapter | None = None

_OCR: OCRAdapter | None = None

_LLM: LLMAdapter | None = None

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===











# ----------------------------- Globals (private) -----------------------------


# ------------------------------- Factories ----------------------------------


def _make_drive() -> DriveAdapter:
    """

    PL: Lokalny storage pod ./static, URL prefix /static (zgodne z API).

    EN: Local storage under ./static, URL prefix /static (aligned with API).

    """

    base_dir = Path("static")

    return LocalDriveAdapter(base_dir=base_dir, base_url_prefix="/static")


def _make_preview(drive: DriveAdapter) -> PreviewAdapter:
    """

    PL: Stub preview (DOCX→PDF placeholder).

    EN: Stub preview (DOCX→PDF placeholder).

    """

    return StubPreviewAdapter(cast(LocalDriveAdapter, drive))


def _make_ocr() -> OCRAdapter:
    """

    PL: Stub OCR (jedna strona z heurystyką).

    EN: Stub OCR (single page with heuristic).

    """

    return StubOCRAdapter()


def _make_llm() -> LLMAdapter:
    """

    PL: Deterministyczny ALI-Stub dla /v1/analyze.

    EN: Deterministic ALI-Stub for /v1/analyze.

    """

    return StubLLMAdapter(model_name="ALI-Stub-0")


# -------------------------------- Getters -----------------------------------


def get_drive() -> DriveAdapter:
    """PL/EN: Lazy singleton for DriveAdapter."""

    global _DRIVE

    if _DRIVE is None:
        _DRIVE = _make_drive()

    return _DRIVE


def get_preview() -> PreviewAdapter:
    """PL/EN: Lazy singleton for PreviewAdapter."""

    global _PREVIEW

    if _PREVIEW is None:
        _PREVIEW = _make_preview(get_drive())

    return _PREVIEW


def get_ocr() -> OCRAdapter:
    """PL/EN: Lazy singleton for OCRAdapter."""

    global _OCR

    if _OCR is None:
        _OCR = _make_ocr()

    return _OCR


def get_llm() -> LLMAdapter:
    """PL/EN: Lazy singleton for LLMAdapter."""

    global _LLM

    if _LLM is None:
        _LLM = _make_llm()

    return _LLM



# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

