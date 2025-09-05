# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/models.py                   |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/models.py                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

# +-------------------------------------------------------------+

# |                        CERTEUS                              |

# |        Core Engine for Reliable & Unified Systems           |

# +-------------------------------------------------------------+

"""

PL: Ten moduł definiuje atomową jednostkę informacji w CERTEUS: **Fact**.

    To „waluta” przekazywana do Jądra Prawdy. Model jest rygorystyczny,

    wersjonowany (schema_version) i odporny na śmieci w polach

    (extra="forbid").

EN: This module defines the atomic unit of information in CERTEUS: **Fact**.

    It is the “currency” passed into the Truth Engine. The model is strict,

    versioned (schema_version), and resilient to junk fields

    (extra="forbid").

Zgodność stylistyczna:

- nagłówek ASCII, opisy PL/EN, podpisane bloki.

Style compliance:

- ASCII header, PL/EN docs, labeled blocks.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from datetime import date
from enum import Enum
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

class FactRole(str, Enum):
    """

    PL: Enum ról faktów – jasno nazywa funkcję faktu w analizie.

    EN: Fact roles – clearly naming the function of a fact in analysis.

    """

    # PL: twierdzenie dot. daty umowy / EN: contract date claim

    claim_contract_date = "claim_contract_date"

    # PL: dowód wpłaty / EN: proof of payment

    evidence_payment = "evidence_payment"

class Fact(BaseModel):
    """

    PL: Reprezentuje pojedynczy, ustrukturyzowany fakt wydobyty z dokumentu.

        • schema_version – wersjonowanie schematu (migracje wstecznie bezpieczne).

        • role – rola faktu w konstrukcji prawnej/argumentacyjnej.

        • event_date – data zdarzenia (opcjonalna, gdy możliwa ekstrakcja).

        • thesis – treść faktu; zwięzła, jednoznaczna; bez retoryki.

        • source_document_hash – sha256:... wskazujący oryginał.

        • source_page – numer strony w źródle (≥ 1).

        • confidence_score – pewność ekstrakcji [0.0, 1.0].

    EN: Represents a single, structured fact extracted from a document.

        • schema_version – schema versioning (backward-safe migrations).

        • role – the fact’s function in legal/argument structure.

        • event_date – date of the event (optional, if extractable).

        • thesis – fact content; concise and unambiguous; no rhetoric.

        • source_document_hash – sha256:... pointing to the source.

        • source_page – page number in source (≥ 1).

        • confidence_score – extraction confidence [0.0, 1.0].

    """

    # Rygorystyczna konfiguracja: odrzucaj pola nieznane

    # Strict config: forbid unknown fields

    model_config = ConfigDict(extra="forbid")

    # Wersja schematu / Schema version

    schema_version: Literal["1.0"] = "1.0"

    # Identyfikacja i semantyka / Identification and semantics

    fact_id: str = Field(
        ...,
        description=("PL: Unikalny identyfikator faktu. | EN: Unique identifier for the fact."),
    )

    role: FactRole = Field(
        ...,
        description="PL: Rola faktu w sprawie. | EN: Role of the fact in the case.",
    )

    event_date: date | None = Field(
        None,
        description=("PL: Data zdarzenia (opcjonalna). | EN: Date of the event (optional)."),
    )

    # Treść i źródło / Content and source

    thesis: str = Field(
        ...,
        min_length=3,
        description="PL: Treść faktu. | EN: The content of the fact.",
    )

    source_document_hash: str = Field(
        ...,
        pattern=r"^sha256:[0-9a-f]{64}$",
        description=("PL: Hash dokumentu źródłowego (sha256:...). | EN: Source document hash (sha256:...)."),
    )

    source_page: int | None = Field(
        None,
        ge=1,
        description=("PL: Numer strony w źródle (≥1). | EN: Source page number (≥1)."),
    )

    # Jakość ekstrakcji / Extraction quality

    confidence_score: float = Field(
        ...,
        ge=0.0,
        le=1.0,
        description=("PL: Pewność ekstrakcji [0.0–1.0]. | EN: Extraction confidence [0.0–1.0]."),
    )

# === LOGIKA / LOGIC ===

# [BLOCK: IMPORTS / IMPORTY]

# [BLOCK: ENUMS / ENUMERACJE]

# [BLOCK: MODELS / MODELE]

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
