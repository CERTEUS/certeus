# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/law_as_data/adapters/isap.py               |

# | ROLE: Project module.                                       |

# | PLIK: services/law_as_data/adapters/isap.py               |

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
import re

from ..cache import FileCache, cache_from_uri


@dataclass
class LawDocument:
    uri: str

    digest: str

    path: str

    title: str | None = None


_TITLE_RE = re.compile(r"<title>(.*?)</title>", re.IGNORECASE | re.DOTALL)


def extract_title(html_bytes: bytes) -> str | None:
    try:
        m = _TITLE_RE.search(html_bytes.decode("utf-8", errors="ignore"))

        return m.group(1).strip() if m else None

    except Exception:
        return None


def fetch_and_cache_isap(uri: str, cache: FileCache | None = None) -> LawDocument:
    cs = cache_from_uri(uri, cache)

    title = None

    try:
        title = extract_title(cs.path.read_bytes())

    except Exception:
        title = None

    return LawDocument(uri=cs.uri, digest=cs.digest, path=str(cs.path), title=title)
