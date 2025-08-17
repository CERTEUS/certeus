# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/utils/test_console.py             |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/utils/test_console.py                           |
# | ROLE: Tests for console utilities (ASCII-safe & colors).    |
# | PLIK: tests/utils/test_console.py                           |
# | ROLA: Testy narzędzi konsolowych (ASCII-safe i kolory).     |
# +-------------------------------------------------------------+
"""
PL: Testy funkcji utils.console: ascii_safe, print_safe, info/success/error i bezpieczeństwo ASCII.
EN: Tests for utils.console functions: ascii_safe, print_safe, info/success/error and ASCII safety.
"""

from __future__ import annotations

from utils.console import ascii_safe, error, info, print_safe, success


class _AsciiOnlyStream:
    """Tiny write-capturing stream that only accepts ASCII."""

    def __init__(self) -> None:
        self._encoding = "ascii"
        self._buf: list[str] = []

    @property
    def encoding(self) -> str:  # Protocol dopuszcza Optional[str]
        return self._encoding

    # NAZWA PARAMETRU MUSI BYĆ 's', żeby zgadzała się z Protocol.StreamLike
    def write(self, s: str) -> int:
        # enforce ASCII-only
        s.encode("ascii")
        self._buf.append(s)
        return len(s)

    def flush(self) -> None:  # pragma: no cover
        return

    def getvalue(self) -> str:
        return "".join(self._buf)

    def isatty(self) -> bool:  # pragma: no cover
        return False


def test_ascii_safe_true_for_ascii_stream() -> None:
    s = _AsciiOnlyStream()
    assert ascii_safe(s) is True


def test_print_safe_replaces_non_ascii_on_ascii_stream() -> None:
    s = _AsciiOnlyStream()
    text = "Zażółć gęślą jaźń"
    print_safe(text, stream=s)  # should not raise
    captured = s.getvalue()
    # enforce that output is pure ASCII
    captured.encode("ascii")
    # and likely contains replacements
    assert any(ord(ch) > 127 for ch in text)
    assert "?" in captured or captured != text


def test_info_success_error_prefixes_ascii_stream() -> None:
    s = _AsciiOnlyStream()
    info("hello", stream=s)
    success("world", stream=s)
    error("boom", stream=s)
    out = s.getvalue()
    assert "[INFO] " in out
    assert "[SUCCESS] " in out
    assert "[ERROR] " in out
