# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/law_as_data/cache.py                       |

# | ROLE: Project module.                                       |

# | PLIK: services/law_as_data/cache.py                       |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import time
import urllib.request

from monitoring.metrics_slo import certeus_source_fetch_errors_total


def compute_digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


@dataclass
class CachedSource:
    uri: str

    digest: str

    path: Path

    retrieved_at: str


class FileCache:
    """

    Minimal Law-as-Data file cache with digests.

    Stores payloads under data/law_cache/<digest> and writes index.json.

    """

    def __init__(self, base_dir: Path | None = None) -> None:
        root = Path(os.getenv("LAW_CACHE_DIR") or "./data/law_cache")

        self.base_dir = base_dir or root

        self.base_dir.mkdir(parents=True, exist_ok=True)

        (self.base_dir / "index").mkdir(parents=True, exist_ok=True)

    def _index_path(self, digest: str) -> Path:
        return self.base_dir / "index" / f"{digest}.json"

    def _blob_path(self, digest: str) -> Path:
        return self.base_dir / digest

    def put(self, uri: str, data: bytes) -> CachedSource:
        digest = compute_digest(data)

        blob = self._blob_path(digest)

        blob.write_bytes(data)

        meta = {
            "uri": uri,
            "digest": digest,
            "path": str(blob.resolve()),
            "retrieved_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }

        self._index_path(digest).write_text(
            json.dumps(meta, ensure_ascii=False, indent=2), encoding="utf-8"
        )

        return CachedSource(
            uri=uri, digest=digest, path=blob, retrieved_at=meta["retrieved_at"]
        )

    def get(self, digest: str) -> CachedSource | None:
        idx = self._index_path(digest)

        if not idx.exists():
            return None

        raw = json.loads(idx.read_text(encoding="utf-8"))

        return CachedSource(
            uri=raw["uri"],
            digest=raw["digest"],
            path=Path(raw["path"]),
            retrieved_at=raw["retrieved_at"],
        )


def _fetch_uri(uri: str) -> bytes:
    try:
        with urllib.request.urlopen(uri) as resp:  # nosec - trusted adapter path only
            return resp.read()

    except Exception:
        try:
            certeus_source_fetch_errors_total.inc()

        except Exception:
            pass

        raise


def cache_from_uri(uri: str, cache: FileCache | None = None) -> CachedSource:
    c = cache or FileCache()

    data = _fetch_uri(uri)

    return c.put(uri, data)
