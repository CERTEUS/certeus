#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_sources_cache.py                |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_sources_cache.py                |

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

import json
from pathlib import Path

from fastapi.testclient import TestClient
import pytest

from services.api_gateway.main import app


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
def dummy_urlopen(monkeypatch: pytest.MonkeyPatch):
    def _set(data: bytes) -> None:
        def _urlopen(_uri: str):  # type: ignore[override]
            return DummyResponse(data)

        import urllib.request as _ur

        monkeypatch.setattr(_ur, "urlopen", _urlopen, raising=True)

    return _set


def test_sources_cache_writes_and_returns_digest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, dummy_urlopen
) -> None:
    # Use a dedicated cache dir

    monkeypatch.setenv("LAW_CACHE_DIR", str(tmp_path))

    dummy_urlopen("USTAWA — TEST DZU".encode())

    client = TestClient(app)

    r = client.post("/v1/sources/cache", json={"uri": "https://isap.sejm.gov.pl/some-act"})

    assert r.status_code == 200

    body = r.json()

    assert body["digest"]

    # index file exists

    idx = Path(tmp_path) / "index" / f"{body['digest']}.json"

    assert idx.exists()

    meta = json.loads(idx.read_text(encoding="utf-8"))

    assert meta["uri"].startswith("https://")
