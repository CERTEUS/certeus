# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: utils/console.py                                    |

# | ROLE: Project module.                                       |

# | PLIK: utils/console.py                                    |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/utils/console.py                        |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: utils/console.py                                      |

# | ROLE: Console helpers: ASCII-safe printing & colored logs.  |

# | PLIK: utils/console.py                                      |

# | ROLA: Pomocniki konsolowe: druk ASCII-safe i kolorowe logi. |

# +-------------------------------------------------------------+

"""

PL: Funkcje do bezpiecznego wypisywania ASCII oraz proste znaczniki logów

na strumieniach tekstowych (kolorystyczne).

EN: Helpers for ASCII-safe printing and simple colored

log markers on text streams.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

import sys
from typing import Protocol, cast, runtime_checkable

@runtime_checkable
class StreamLike(Protocol):
    @property
    def encoding(self) -> str | None: ...

    def write(self, s: str) -> int: ...

    def flush(self) -> None: ...

    def isatty(self) -> bool: ...

def _normalize_stream(stream: StreamLike | None, *, fallback: object) -> StreamLike:
    """Return a non-None stream that satisfies StreamLike (runtime-checked)."""

    if stream is not None:
        return stream

    # sys.stdout/sys.stderr spełniają protokół w runtime; rzutujemy jawnie.

    return cast(StreamLike, fallback)

def ascii_safe(stream: StreamLike | None = None) -> bool:
    """

    True jeśli strumień obsługuje ASCII/UTF bez problemów kodowania.

    Conservative: brak informacji o kodowaniu => uznaj za „bezpieczny”.

    """

    s = _normalize_stream(stream, fallback=sys.stdout)

    enc = getattr(s, "encoding", None)

    if enc is None:
        return True

    enc_low = enc.lower()

    return enc_low == "ascii" or enc_low.startswith("utf")

def print_safe(text: str, stream: StreamLike | None = None) -> None:
    """

    Wypisz tekst tak, by nie wywalał się na Windowsowych „charmap”.

    Dla strumieni ASCII zamieniamy znaki nie-ASCII na '?'.

    """

    s = _normalize_stream(stream, fallback=sys.stdout)

    enc = getattr(s, "encoding", None)

    out = text

    if enc and enc.lower() == "ascii":
        out = out.encode("ascii", "replace").decode("ascii")

    s.write(out)

    try:
        s.flush()

    except Exception:
        # Faux-stream może nie mieć flush; ignorujemy.

        return

def _color(prefix: str, code: str, *, stream: StreamLike) -> str:
    """Koloruj prefiks tylko, jeśli TTY; inaczej zwróć zwykły tekst."""

    if getattr(stream, "isatty", lambda: False)():
        return f"\x1b[{code}m{prefix}\x1b[0m "

    return f"{prefix} "

def info(msg: str, stream: StreamLike | None = None) -> None:
    s = _normalize_stream(stream, fallback=sys.stdout)

    prefix = _color("[INFO]", "94", stream=s)

    print_safe(prefix + msg, stream=s)

def success(msg: str, stream: StreamLike | None = None) -> None:
    s = _normalize_stream(stream, fallback=sys.stdout)

    prefix = _color("[SUCCESS]", "92", stream=s)

    print_safe(prefix + msg, stream=s)

def error(msg: str, stream: StreamLike | None = None) -> None:
    s = _normalize_stream(stream, fallback=sys.stderr)

    prefix = _color("[ERROR]", "91", stream=s)

    print_safe(prefix + msg, stream=s)
