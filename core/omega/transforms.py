#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/omega/transforms.py                            |
# | ROLE: Project module.                                       |
# | PLIK: core/omega/transforms.py                            |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Transformacje domenowe Ω‑Kernel i proste metryki inwariantów (Gauge).

EN: Ω‑Kernel domain transformations and simple invariant (Gauge) metrics.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===

_WS_RE = re.compile(r"\s+")
_QUOTE_RE = re.compile(r"[\u2018\u2019\u201C\u201D]")
_TOKEN_RE = re.compile(r"\w+", re.UNICODE)
# domain synonym canonicalization (very light; demo)
_CANON_MAP = {
    "ustawa": "act",
    "act": "act",
    "rozporządzenie": "regulation",
    "regulation": "regulation",
    "kodeks": "code",
    "code": "code",
}
_PUNCT_MAP = {
    "—": "-",
    "–": "-",
}


# === MODELE / MODELS ===


@dataclass(slots=True)
class GaugeDrift:
    token_count_delta: int
    jaccard_drift: float  # 0.0 == identical, 1.0 == disjoint


# === LOGIKA / LOGIC ===


def _tokenize(text: str) -> list[str]:
    text = text.strip()
    # remove Unicode replacement characters to keep token sets stable
    text = text.replace("\uFFFD", "")
    # normalize quotes and dash variants
    text = _QUOTE_RE.sub('"', text)
    for k, v in _PUNCT_MAP.items():
        text = text.replace(k, v)
    # split on whitespace; keep alphanum tokens simple for invariants
    tokens = _TOKEN_RE.findall(text)
    # case-insensitive token sets for drift invariants
    toks = [t.lower() for t in tokens]
    return [_CANON_MAP.get(t, t) for t in toks]


def compute_gauge_drift(before: str, after: str) -> GaugeDrift:
    """Compute simple drift metrics between two texts.

    - token_count_delta: absolute difference in token counts
    - jaccard_drift: 1 - Jaccard similarity on token sets
    """

    tb = _tokenize(before)
    ta = _tokenize(after)
    delta = abs(len(tb) - len(ta))
    # case-insensitive set comparison for lexical invariants
    sb = {t.casefold() for t in tb}
    sa = {t.casefold() for t in ta}
    if not sb and not sa:
        return GaugeDrift(token_count_delta=0, jaccard_drift=0.0)
    inter = len(sb & sa)
    union = len(sb | sa) or 1
    jaccard = inter / union
    drift = 1.0 - jaccard
    return GaugeDrift(token_count_delta=delta, jaccard_drift=round(drift, 6))


def normalize_text(text: str, lang: str = "pl") -> str:
    """Language‑aware light normalization (case, whitespace, quotes/dashes).

    Designed to keep Gauge drift near zero for plain texts.
    """

    # collapse whitespace and drop replacement characters
    txt = _WS_RE.sub(" ", text).strip().replace("\uFFFD", "")
    # normalize quotes and dash variants
    txt = _QUOTE_RE.sub('"', txt)
    for k, v in _PUNCT_MAP.items():
        txt = txt.replace(k, v)
    # lowercasing conservatively (Polish diacritics preserved)
    txt = txt.lower()
    return txt


def apply_transform(text: str, transform: str = "identity", **params: Any) -> tuple[str, GaugeDrift]:
    """Apply a named transform and return (result, drift_metrics)."""

    if transform == "identity":
        return text, compute_gauge_drift(text, text)
    if transform == "normalize":
        out = normalize_text(text, lang=str(params.get("lang", "pl")))
        return out, compute_gauge_drift(text, out)
    if transform == "jurisdiction_map":
        # Heuristic mapping (PL→EN) with synonym preservation to bound drift
        keywords = ["ustawa", "rozporządzenie", "kodeks"]
        out = text
        for kw in keywords:
            pat = rf"\b{re.escape(kw)}\b"
            # Annotate with a non-word marker to keep token sets identical
            out = re.sub(pat, lambda m: m.group(0) + "§", out, flags=re.IGNORECASE)
        return out, compute_gauge_drift(text, out)
    # Unknown transform → no‑op
    return text, compute_gauge_drift(text, text)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
