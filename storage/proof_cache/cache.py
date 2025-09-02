# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: storage/proof_cache/cache.py                                  |
# | ROLE:                                                               |
# |  PL: Klucze cache PCO (czasowe kubełki 6h).                         |
# |  EN: PCO cache keys (6h time buckets).                              |
# +=====================================================================+

"""PL: cache_key = ruleset|query|ctx|jurisdiction|pack|bucket. EN: see above."""

from __future__ import annotations

import hashlib
import math
import time


def time_bucket(now: float, seconds: int = 21600) -> str:
    """PL: Wiadro czasowe 6h. EN: 6-hour time bucket."""
    # === IMPORTY / IMPORTS ===
    # === KONFIGURACJA / CONFIGURATION ===
    # === MODELE / MODELS ===
    # === LOGIKA / LOGIC ===
    # === I/O / ENDPOINTS ===
    # === TESTY / TESTS ===

    return str(int(math.floor(now / seconds)))


def cache_key(
    ruleset_hash: str, query_hash: str, ctx_hash: str, jurisdiction: str, norm_pack_id: str, now: float | None = None
) -> str:
    """PL: Oblicz klucz cache. EN: Compute cache key."""
    if now is None:
        now = time.time()
    tb = time_bucket(now)
    raw = "|".join([ruleset_hash, query_hash, ctx_hash, jurisdiction, norm_pack_id, tb])
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()
