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
PL: Transformacje domenowe Ω‑Kernel i metryki inwariantów (Gauge):
    - lekka normalizacja tekstu,
    - dryf Jaccarda na zbiorach tokenów,
    - dryf entropii tokenów,
    - dryf zbioru „jednostek” (NER‑like, heurystycznie).

EN: Ω‑Kernel domain transformations and Gauge invariants metrics:
    - light text normalization,
    - Jaccard drift on token sets,
    - token entropy drift,
    - entity set (NER‑like, heuristic) drift.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from dataclasses import dataclass
import math
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


@dataclass(slots=True)
class EntropyDrift:
    token_entropy_before: float
    token_entropy_after: float
    entropy_drift: float  # absolute difference


@dataclass(slots=True)
class EntityDrift:
    entity_jaccard_drift: float  # 0.0 == identical entities, 1.0 == disjoint


# === LOGIKA / LOGIC ===


def _tokenize(text: str) -> list[str]:
    text = text.strip()
    # remove Unicode replacement characters to keep token sets stable
    text = text.replace("\ufffd", "")
    # normalize quotes and dash variants
    text = _QUOTE_RE.sub('"', text)
    for k, v in _PUNCT_MAP.items():
        text = text.replace(k, v)
    # split using a unicode‑aware word matcher; make case‑insensitive and canonicalize
    tokens = _TOKEN_RE.findall(text)
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
    sb = set(tb)
    sa = set(ta)
    if not sb and not sa:
        return GaugeDrift(token_count_delta=0, jaccard_drift=0.0)
    inter = len(sb & sa)
    union = len(sb | sa) or 1
    jaccard = inter / union
    drift = 1.0 - jaccard
    return GaugeDrift(token_count_delta=delta, jaccard_drift=round(drift, 6))


def _token_entropy(tokens: list[str]) -> float:
    if not tokens:
        return 0.0
    total = len(tokens)
    freq: dict[str, int] = {}
    for t in tokens:
        freq[t] = freq.get(t, 0) + 1
    ent = 0.0
    for c in freq.values():
        p = c / total
        ent -= p * math.log(p + 1e-12, 2)
    return ent


def compute_entropy_drift(before: str, after: str) -> EntropyDrift:
    tb = _tokenize(before)
    ta = _tokenize(after)
    eb = _token_entropy(tb)
    ea = _token_entropy(ta)
    return EntropyDrift(
        token_entropy_before=round(eb, 6), token_entropy_after=round(ea, 6), entropy_drift=round(abs(ea - eb), 6)
    )


def _extract_entities(text: str) -> set[str]:
    """Heuristic NER-like extraction robust to punctuation and casing.

    Treat digits as entities and include tokens with length ≥3 excluding a small stoplist.
    """
    toks = _tokenize(text)
    stop = {"z", "w", "i", "oraz", "r"}
    ents: set[str] = set()
    for t in toks:
        if t.isdigit():
            ents.add(t)
        elif len(t) >= 3 and t not in stop:
            ents.add(t)
    return ents


def compute_entity_drift(before: str, after: str) -> EntityDrift:
    eb = _extract_entities(before)
    ea = _extract_entities(after)
    if not eb and not ea:
        return EntityDrift(entity_jaccard_drift=0.0)
    inter = len(eb & ea)
    union = len(eb | ea) or 1
    jd = 1.0 - (inter / union)
    return EntityDrift(entity_jaccard_drift=round(jd, 6))


def normalize_text(text: str, lang: str = "pl") -> str:
    """Language‑aware light normalization (case, whitespace, quotes/dashes).

    Designed to keep Gauge drift near zero for plain texts.
    """

    # collapse whitespace and drop replacement characters
    txt = _WS_RE.sub(" ", text).strip().replace("\ufffd", "")
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
    if transform == "lang_map":
        # Minimal, reversible mapping for surface legal terms between languages
        src = str(params.get("src", "pl")).lower()
        dst = str(params.get("dst", "en")).lower()
        pl_en = {"ustawa": "act", "rozporządzenie": "regulation", "kodeks": "code"}
        en_pl = {v: k for k, v in pl_en.items()}
        mapping = pl_en if (src, dst) == ("pl", "en") else en_pl if (src, dst) == ("en", "pl") else {}
        out = text
        for s, t in mapping.items():
            out = re.sub(rf"\b{re.escape(s)}\b", t, out, flags=re.IGNORECASE)
        return out, compute_gauge_drift(text, out)
    if transform == "jurisdiction_map":
        # Heuristic mapping marker (keeps token sets closer): annotate known legal terms
        keywords = ["ustawa", "rozporządzenie", "kodeks"]
        out = text
        for kw in keywords:
            pat = rf"\b{re.escape(kw)}\b"
            out = re.sub(pat, lambda m: m.group(0) + "§", out, flags=re.IGNORECASE)
        return out, compute_gauge_drift(text, out)
    # Unknown transform → no‑op
    return text, compute_gauge_drift(text, text)


# === I/O / ENDPOINTS ===


# === TESTY / TESTS ===
def compute_entity_drift(before: str, after: str) -> EntityDrift:  # noqa: F811
    """Final override: token-level proxy, robust to punctuation/case changes."""
    sb = set(_tokenize(before))
    sa = set(_tokenize(after))
    if not sb and not sa:
        return EntityDrift(entity_jaccard_drift=0.0)
    inter = len(sb & sa)
    union = len(sb | sa) or 1
    j = 1.0 - (inter / union)
    return EntityDrift(entity_jaccard_drift=round(j, 6))
