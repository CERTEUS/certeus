# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: governance/pcu_breakglass.py                                  |
# | ROLE:                                                               |
# |  PL: Procedura Break-Glass (TTL ≤14 dni) + log Merkle.              |
# |  EN: Break-Glass procedure (TTL ≤14 days) + Merkle log.             |
# +=====================================================================+

"""PL: Otwieranie i odwołanie Break-Glass z logiem. EN: Open/revoke with logging."""

from __future__ import annotations

from datetime import UTC, datetime, timedelta

MAX_TTL_DAYS = 14


def approve_break_glass(request_id: str, reason: str, until: datetime, merkle_log: list[dict[str, str]]) -> bool:
    """PL: Zgoda na BG. EN: Approve BG."""
    # === IMPORTY / IMPORTS ===
    # === KONFIGURACJA / CONFIGURATION ===
    # === MODELE / MODELS ===
    # === LOGIKA / LOGIC ===
    # === I/O / ENDPOINTS ===
    # === TESTY / TESTS ===

    now = datetime.now(UTC)
    if until - now > timedelta(days=MAX_TTL_DAYS):
        raise ValueError("Break-Glass TTL exceeds 14 days.")
    merkle_log.append(
        {
            "type": "break_glass_open",
            "request_id": request_id,
            "reason": reason,
            "until": until.isoformat(),
        }
    )
    return True


def revoke_break_glass(request_id: str, merkle_log: list[dict[str, str]]) -> bool:
    """PL: Odwołaj BG. EN: Revoke BG."""
    merkle_log.append(
        {
            "type": "break_glass_revoke",
            "request_id": request_id,
            "ts": datetime.now(UTC).isoformat(),
        }
    )
    return True
