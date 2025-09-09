#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/proofs/normalize.py                             |
# | ROLE: Proof normalizer (DRAT trim + LFSC recheck stubs)      |
# +-------------------------------------------------------------+

from __future__ import annotations

from collections.abc import Iterable


def trim_drat(text: str) -> str:
    """PL/EN: Przytnij DRAT do kanonicznej postaci.

    - usuń komentarze (linie zaczynające się od 'c' lub '#')
    - usuń puste linie i nadmiarowe spacje
    - deduplikuj identyczne linie przy zachowaniu kolejności pierwszego wystąpienia

    EN: Normalize DRAT-like text: drop comments/empty lines/extra spaces and
    de-duplicate identical lines while keeping the first occurrence order.
    """

    seen: set[str] = set()
    out: list[str] = []
    for raw in _iter_lines(text):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("c") or line.startswith("#"):
            # comment line
            continue
        # collapse internal whitespace
        parts = line.split()
        line = " ".join(parts)
        if line in seen:
            continue
        seen.add(line)
        out.append(line)
    return "\n".join(out) + ("\n" if out else "")


def recheck_lfsc(lfsc_text: str) -> bool:
    """PL/EN: Lekki re-checker LFSC (stub).

    Bez pełnego weryfikatora – sprawdza minimalną strukturę (niepusty tekst)
    i rozsądny rozmiar. Zwraca True gdy tekst wygląda na poprawny.

    EN: Lightweight LFSC re-check stub: returns True for non-empty, sane text.
    """

    if not isinstance(lfsc_text, str):
        return False
    lf = lfsc_text.strip()
    if len(lf) < 2:
        return False
    # very loose sanity: must contain at least one parenthesis or space-separated token
    return any(ch in lf for ch in ("(", ")", " "))


def _iter_lines(text: str) -> Iterable[str]:
    # normalize common CRLF/CR cases implicitly by splitlines
    yield from (text or "").splitlines()


# === TESTY / TESTS ===
