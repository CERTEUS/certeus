# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/__init__.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/__init__.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/services/ingest_service/__init__.py     |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


# +-------------------------------------------------------------+

# |                        CERTEUS                              |

# |        Core Engine for Reliable & Unified Systems           |

# +-------------------------------------------------------------+

# ── CERTEUS Project ─────────────────────────────────────────────────────────────

# File: services/ingest_service/__init__.py

# License: Apache-2.0

# Description (PL): Pakiet serwisu ingestii (FACTLOG): eksportuje główne typy.

# Description (EN): Ingestion service package (FACTLOG): exports main types.

# Style Guide: ASCII header, PL/EN docs, labeled code blocks. (See README)

# ────────────────────────────────────────────────────────────────────────────────


"""

PL: Pakiet serwisu ingestii. Ten moduł oznacza pakiet Pythona oraz

    udostępnia publiczny interfejs (eksport) najczęściej używanych typów.

EN: Ingestion service package. This module marks the Python package and

    exposes a public interface (exports) of the most commonly used types.

"""


# [BLOCK: PUBLIC API EXPORTS / EKSPORT INTERFEJSU PUBLICZNEGO]

from .models import Fact, FactRole

__all__ = ["Fact", "FactRole"]
