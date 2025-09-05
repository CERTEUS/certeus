# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: monitoring/metrics_goodhart.py                                |
# | ROLE:                                                               |
# |  PL: Liczniki Goodhart (novel/contradictions).                      |
# |  EN: Goodhart counters (novel/contradictions).                      |
# +=====================================================================+

"""PL: Eksport liczników do /metrics. EN: Export counters to /metrics."""

from __future__ import annotations

from prometheus_client import Counter

truth_novel_case_rate = Counter("truth_novel_case_rate", "Novel case detections")
truth_contradiction_rate = Counter("truth_contradiction_rate", "Contradictions detected")

def observe_novel_case() -> None:
    """PL: Zgłoś nowy przypadek. EN: Report novel case."""
    # === IMPORTY / IMPORTS ===
    # === KONFIGURACJA / CONFIGURATION ===
    # === MODELE / MODELS ===
    # === LOGIKA / LOGIC ===
    # === I/O / ENDPOINTS ===
    # === TESTY / TESTS ===

    truth_novel_case_rate.inc()

def observe_contradiction() -> None:
    """PL: Zgłoś sprzeczność. EN: Report contradiction."""
    truth_contradiction_rate.inc()
