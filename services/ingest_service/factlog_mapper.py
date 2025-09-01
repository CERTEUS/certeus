# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/factlog_mapper.py           |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/factlog_mapper.py           |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Ten moduł przekształca surowy wynik OCR w listę faktów zgodnych z modelem

    `Fact`. Jest to stub reguł: wykrywa dwie proste przesłanki i przypisuje im

    stałe wartości. Wersja docelowa użyje NLP/NLU.



EN: This module transforms raw OCR output into a list of `Fact` objects.

    It is a rule-based stub: it detects two simple premises and assigns

    fixed values. The production version will use NLP/NLU.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from datetime import date

import hashlib

from typing import Any

import uuid

from .models import Fact, FactRole

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===
class FactlogMapper:
    """

    PL: Przekształca dane z OCR na ustrukturyzowane fakty.

    EN: Transforms OCR data into structured facts.

    """

    def map_to_facts(self, ocr_output: dict[str, Any], document_bytes: bytes) -> list[Fact]:
        """

        PL:

        - Buduje hash dokumentu (chain-of-custody).

        - Na podstawie prostych reguł tworzy listę faktów.



        EN:

        - Builds a document hash (chain-of-custody).

        - Creates a list of facts using simple rules.

        """

        document_hash = _sha256_hex(document_bytes)

        pages = _pages_by_num(ocr_output)

        facts: list[Fact] = []

        # [RULE: CONTRACT DATE CLAIM] / [REGUŁA: DATA UMOWY]

        if "umowa została zawarta" in pages.get(1, ""):
            facts.append(
                Fact(
                    fact_id=f"fact-{uuid.uuid4()}",
                    role=FactRole.claim_contract_date,
                    event_date=date(2024, 1, 15),
                    thesis="Umowa została zawarta dnia 2024-01-15.",
                    source_document_hash=document_hash,
                    source_page=1,
                    confidence_score=0.95,
                )
            )

        # [RULE: PROOF OF PAYMENT] / [REGUŁA: DOWÓD WPŁATY]

        if "Dowód wpłaty" in pages.get(2, ""):
            facts.append(
                Fact(
                    fact_id=f"fact-{uuid.uuid4()}",
                    role=FactRole.evidence_payment,
                    event_date=None,  # Pylance appeasement: explicit optional
                    thesis="Istnieje dowód wpłaty na 5000 PLN.",
                    source_document_hash=document_hash,
                    source_page=2,
                    confidence_score=0.99,
                )
            )

        return facts

# === LOGIKA / LOGIC ===



















# [BLOCK: IMPORTS / IMPORTY]


# [BLOCK: HELPERS / POMOCNICZE]


def _sha256_hex(data: bytes) -> str:
    """PL/EN: Returns sha256:... digest for given bytes."""

    return "sha256:" + hashlib.sha256(data).hexdigest()


def _pages_by_num(ocr_output: dict[str, Any]) -> dict[int, str]:
    """PL/EN: Maps page_num -> text."""

    return {p.get("page_num"): p.get("text", "") for p in ocr_output.get("pages", [])}


# [BLOCK: MAPPER / MAPOWANIE]





# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

