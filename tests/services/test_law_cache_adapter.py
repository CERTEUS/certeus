#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_law_cache_adapter.py            |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_law_cache_adapter.py            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from collections.abc import Callable
import json
from pathlib import Path

import pytest

from services.law_as_data.cache import FileCache, cache_from_uri


class DummyResponse:
    def __init__(self, data: bytes) -> None:
        self._data = data

    def read(self) -> bytes:
        return self._data

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False


@pytest.fixture()
def dummy_urlopen(monkeypatch: pytest.MonkeyPatch) -> Callable[[bytes], None]:
    def _set(data: bytes) -> None:
        def _urlopen(_uri: str):  # type: ignore[override]
            return DummyResponse(data)

        import urllib.request as _ur

        monkeypatch.setattr(_ur, "urlopen", _urlopen, raising=True)

    return _set


def test_cache_from_uri_writes_blob_and_index(tmp_path: Path, dummy_urlopen) -> None:
    dummy_urlopen(b"USTAWA: TEST")

    c = FileCache(tmp_path)

    cs = cache_from_uri("https://example.test/law/1", c)

    assert cs.digest

    assert cs.path.exists()

    idx = tmp_path / "index" / f"{cs.digest}.json"

    assert idx.exists()

    meta = json.loads(idx.read_text(encoding="utf-8"))

    assert meta["uri"].startswith("https://example.test/")
