# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: storage/proof_cache/cache.py                                  |
# | ROLE:                                                               |
# |  PL: Klucze cache PCO (czasowe kubełki 6h).                         |
# |  EN: PCO cache keys (6h time buckets).                              |
# +=====================================================================+

"""
PL: Moduł obliczający klucze pamięci podręcznej (cache) dla PCO.
    Format klucza: ruleset|query|ctx|jurisdiction|pack|bucket, gdzie bucket
    to kubełek czasowy o szerokości 6 godzin.

EN: Module for computing cache keys for PCO.
    Key format: ruleset|query|ctx|jurisdiction|pack|bucket, where bucket
    is a 6-hour time bucket.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import hashlib
import math
import time

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

def time_bucket(now: float, seconds: int = 21600) -> str:
    """PL: Wiadro czasowe 6h. EN: 6-hour time bucket."""
    return str(int(math.floor(now / seconds)))

def cache_key(
    ruleset_hash: str,
    query_hash: str,
    ctx_hash: str,
    jurisdiction: str,
    norm_pack_id: str,
    now: float | None = None,
) -> str:
    """PL: Oblicz klucz cache. EN: Compute cache key."""
    if now is None:
        now = time.time()
    tb = time_bucket(now)
    raw = "|".join([ruleset_hash, query_hash, ctx_hash, jurisdiction, norm_pack_id, tb])
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
