"""PL: Harmonogram odświeżania dowodów (prawo=365, med=90, fin=7).
EN: Re-proof scheduler (law=365, med=90, fin=7).
"""

# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: scripts/temporal_fortress.py                                  |
# | ROLE:                                                               |
# |  PL: Re-proof po TTL (TTDE) per domena.                             |
# |  EN: TTDE re-proof per domain TTL.                                  |
# +=====================================================================+

from __future__ import annotations

from datetime import UTC, datetime, timedelta

TTL_DAYS: dict[str, int] = {"prawo": 365, "med": 90, "fin": 7}


def due(domain: str, last_proof_at: datetime) -> bool:
    """PL: Czy wygasło TTL? EN: TTL expired?"""
    days = TTL_DAYS.get(domain, 365)
    return datetime.now(UTC) - last_proof_at > timedelta(days=days)


def run() -> None:
    """PL: Znajdź kapsuły do re-proof i zleć zadania. EN: Enqueue due re-proofs."""
    # Integracja z magazynem kapsuł (do uzupełnienia zgodnie z repo).
    # Keeping architecture unchanged.
    return
