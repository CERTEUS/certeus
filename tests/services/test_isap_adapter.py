#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_isap_adapter.py                 |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_isap_adapter.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path

import pytest

from services.law_as_data.adapters.isap import extract_title, fetch_and_cache_isap
from services.law_as_data.cache import FileCache


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


def test_extract_title() -> None:
    html = b"<html><head><title>Ustawa Testowa</title></head><body></body></html>"

    assert extract_title(html) == "Ustawa Testowa"


def test_fetch_and_cache_isap_sets_title(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, dummy_urlopen) -> None:
    monkeypatch.setenv("LAW_CACHE_DIR", str(tmp_path))

    dummy_urlopen(b"<html><head><title>Test Dz.U.</title></head></html>")

    c = FileCache(tmp_path)

    doc = fetch_and_cache_isap("https://isap.sejm.gov.pl/isap.nsf/DocDetails.xsp?id=WDU19970880553", c)

    assert doc.title == "Test Dz.U."

    assert Path(doc.path).exists()
