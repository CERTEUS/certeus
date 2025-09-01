# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/adapters/ocr_injector.py    |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/adapters/ocr_injector.py    |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# =============================================================================

#  CERTEUS — OCR Injector (helper for /v1/ingest)

# =============================================================================

#  PL:

#    Lekki helper do pobrania podglądu OCR (pierwsza strona) i zbudowania meta,

#    które można bezpiecznie dołączyć do odpowiedzi /v1/ingest jako "ocr_preview".

#    Domyślnie nie zmienia istniejących pól (2 fakty + X-CERTEUS-Ledger-Chain).

#

#  EN:

#    Lightweight helper to fetch OCR preview (first page) and build a meta dict

#    that can be safely merged into /v1/ingest response under "ocr_preview".

#    It does not alter existing fields (2 facts + X-CERTEUS-Ledger-Chain).

# =============================================================================

"""

PL: Helper do wstrzykiwania skrótu OCR (pierwsza strona) do metadanych.

EN: Helper to inject OCR snippet (first page) into metadata.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

from __future__ import annotations

from typing import Any

from services.ingest_service.adapters.contracts import Blob, OCRRequest
from services.ingest_service.adapters.registry import get_ocr


async def build_ocr_preview(
    blob: Blob,
    *,
    case_id: str | None = None,
    max_chars: int = 400,
) -> dict[str, Any]:
    """

    PL:

      Zwraca słownik z kluczem "ocr_preview" zawierającym skrócony tekst z pierwszej

      strony (stub OCR). Jeśli format nie nadaje się do OCR, zwraca pusty dict.

    EN:

      Returns dict with "ocr_preview" key holding truncated text of the first page

      (stub OCR). If format is not OCR-friendly, returns an empty dict.

    """

    # Heurystyka: tylko obrazy/PDF-y poddajemy OCR; dla innych formatów nic nie robimy.

    ct = (blob.content_type or "").lower()

    is_image = ct.startswith("image/")

    is_pdf = ct == "application/pdf"

    if not (is_image or is_pdf):
        return {}

    pages = await get_ocr().extract(OCRRequest(blob=blob, case_id=case_id or "default"))

    # Bezpiecznie bierzemy tylko pierwszą stronę (stub i tak zwraca jedną).

    first = next(iter(pages), None)

    if first is None or not first.text:
        return {}

    text = first.text.strip()

    if len(text) > max_chars:
        text = text[: max_chars - 1] + "…"

    return {"ocr_preview": text}


def merge_meta(original: dict[str, Any] | None, extra: dict[str, Any]) -> dict[str, Any]:
    """

    PL: Niekolizyjne łączenie metadanych (None → {}), bez nadpisywania istniejących kluczy.

    EN: Non-destructive meta merge (None → {}), without overwriting existing keys.

    """

    base = dict(original or {})

    for k, v in extra.items():
        if k not in base:
            base[k] = v

    return base
