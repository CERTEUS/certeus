# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/ingest_service/ocr_pipeline.py             |
# | ROLE: Project module.                                       |
# | PLIK: services/ingest_service/ocr_pipeline.py             |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+


"""

PL: Ten moduł dostarcza stub potoku OCR na potrzeby F0_D6 (Ingest → FACTLOG).

    Nie wykonuje realnego OCR – zwraca deterministyczne, przewidywalne dane

    testowe. Ma wbudowane: logowanie i limit rozmiaru wejścia (bezpieczeństwo).



EN: This module provides an OCR pipeline stub for F0_D6 (Ingest → FACTLOG).

    It does NOT run real OCR – it returns deterministic, predictable mock data.

    Built-ins: logging and input size guard (safety).

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import logging
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===
DEFAULT_MAX_BYTES = 10 * 1024 * 1024  # 10 MB
logger = logging.getLogger(__name__)


# === MODELE / MODELS ===
class OcrPipeline:
    """

    PL: Stub klasy potoku OCR. Wersja produkcyjna zostanie zastąpiona modułem

        POLON-OCR. Metoda `process_document` przyjmuje bajty pliku oraz

        opcjonalny limit rozmiaru i zwraca ustrukturyzowany wynik.



    EN: Stub OCR pipeline class. The production version will be replaced by

        POLON-OCR. The `process_document` method accepts file bytes and an

        optional size limit, returning a structured result.

    """

    def process_document(self, file_bytes: bytes, *, max_bytes: int = DEFAULT_MAX_BYTES) -> dict[str, Any]:
        """

        PL:

        - Waliduje rozmiar wejścia (domyślnie 10 MB).

        - Zwraca przewidywalny wynik OCR (2 strony, język 'pl').



        EN:

        - Validates input size (10 MB by default).

        - Returns a predictable OCR result (2 pages, language 'pl').

        """

        size = len(file_bytes or b"")

        if size > max_bytes:
            logger.warning("OCR Stub: input too large (%d bytes > %d)", size, max_bytes)

            raise ValueError(f"OCR input too large: {size} > {max_bytes} bytes")

        logger.info("OCR Stub: processing document (%d bytes)…", size)

        # Deterministyczny wynik „OCR”

        # Deterministic mock OCR output

        return {
            "metadata": {
                "page_count": 2,
                "language": "pl",
            },
            "pages": [
                {
                    "page_num": 1,
                    "text": ("Strona 1: Jan Kowalski twierdzi, że umowa została zawarta dnia 2024-01-15."),
                },
                {
                    "page_num": 2,
                    "text": "Strona 2: Dowód wpłaty na kwotę 5000 PLN.",
                },
            ],
        }


# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
