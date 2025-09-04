#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: sitecustomize.py                                     |
# | ROLE: Test/runtime shim.                                    |
# | PLIK: sitecustomize.py                                     |
# | ROLA: Shim runtime/testowy.                                 |
# +-------------------------------------------------------------+
"""
PL: Shim kompatybilności Hypothesis — dodaje wsparcie dla parametru
    `whitespace` w `hypothesis.strategies.characters`, jeżeli nieobecny.
EN: Hypothesis compatibility shim — adds `whitespace` support to
    `hypothesis.strategies.characters` if missing.
"""

from __future__ import annotations

try:
    import hypothesis.strategies as _st  # type: ignore

    _real_characters = _st.characters

    def _characters_compat(*args, **kwargs):  # type: ignore[override]
        # Accept and handle `whitespace=False` by filtering out space characters.
        if "whitespace" in kwargs:
            ws = kwargs.pop("whitespace")
            strat = _real_characters(*args, **kwargs)
            if ws is False:
                return strat.filter(lambda ch: not ch.isspace())
            # ws True/None: leave unchanged
            return strat
        return _real_characters(*args, **kwargs)

    # Patch only if signature doesn't already accept the keyword (best‑effort)
    try:
        _real_characters(whitespace=True)  # type: ignore[call-arg]
    except TypeError:
        _st.characters = _characters_compat  # type: ignore[assignment]
except Exception:
    # Silent no‑op if Hypothesis not installed
    pass
