#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: kernel/mismatch_protocol.py                         |

# | ROLE: Project module.                                       |

# | PLIK: kernel/mismatch_protocol.py                         |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""Protokół uruchamiany przy rozbieżności solverów — tworzy bilet."""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from typing import Any

from services.mismatch_service.service import mismatch_service

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===
class MismatchError(RuntimeError):
    """Rzucane gdy wykryto niezgodność wyników solverów."""


# === LOGIKA / LOGIC ===


def handle_mismatch(case_id: str, formula_str: str, results: dict[str, Any]) -> None:
    ticket = mismatch_service.create_ticket(
        case_id=case_id,
        formula_str=formula_str,
        results=results,
        formula_ast=None,
    )

    raise MismatchError(f"Solver results are inconsistent. See ticket {ticket.ticket_id}.")


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
