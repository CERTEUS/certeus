# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/sipp_indexer_service/models.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/sipp_indexer_service/models.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/services/sipp_indexer_service/models.py |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


# +-------------------------------------------------------------+

# |                         CERTEUS                             |

# |      Core Engine for Reliable & Unified Systems             |

# +-------------------------------------------------------------+

# | FILE: services/sipp_indexer_service/models.py               |

# | ROLE: Pydantic DTOs for SIPP Indexer (LegalActSnapshot).    |

# +-------------------------------------------------------------+


"""

PL: Modele danych Pydantic v2 dla SIPP Indexer.

EN: Pydantic v2 data models for the SIPP Indexer.

"""

from __future__ import annotations

from datetime import date, datetime

from pydantic import BaseModel, Field


class LegalActSnapshot(BaseModel):
    """

    PL: Jedna, zwersjonowana migawka aktu prawnego.

    EN: A single, versioned snapshot of a legal act.

    """

    act_id: str = Field(
        ...,
        description="PL: Id aktu (np. 'kk-art-286'). EN: Act identifier (e.g., 'kk-art-286').",
    )

    version_id: str = Field(
        ...,
        description="PL: Id wersji (np. data publikacji). EN: Version id (e.g., publication date).",
    )

    text_sha256: str = Field(
        ...,
        description="PL: SHA256 tekstu wersji aktu. EN: SHA256 of act text for this version.",
    )

    source_url: str = Field(
        ...,
        description="PL: Oficjalny URL (np. ISAP). EN: Official source URL (e.g., ISAP).",
    )

    valid_from: date = Field(
        ...,
        description="PL: Data obowiązywania wersji. EN: Date from which this version is valid.",
    )

    snapshot_timestamp: datetime = Field(
        ...,
        description="PL: Znacznik czasu wykonania migawki. EN: Timestamp of snapshot creation.",
    )
