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

# Domain-specific light canonicalization maps (keep tokens stable)
_DOMAIN_MAPS: dict[str, dict[str, str]] = {
    # Healthcare/Medical (MED) — canonicalize forms in Polish (low drift)
    "med": {
        "leki": "lek",
        "pacjenta": "pacjent",
        "pacjentka": "pacjent",
        "pacjenci": "pacjent",
        "pacjentów": "pacjent",
        "pacjentki": "pacjent",
        # keep base terms as themselves to stabilize token sets
        "lek": "lek",
        "pacjent": "pacjent",
        "dawka": "dawka",
        "dawki": "dawka",
        "dawkowanie": "dawka",
        "choroba": "choroba",
        "choroby": "choroba",
        "objaw": "objaw",
        "objawy": "objaw",
        "diagnoza": "diagnoza",
        "diagnostyka": "diagnoza",
        "terapia": "terapia",
        "terapie": "terapia",
        "lekarz": "lekarz",
        "doktor": "lekarz",
        "dr": "lekarz",
        "szpital": "szpital",
    },
    # Security (SEC) — unify diacritics and common nouns
    "sec": {
        # prefer forms with diacritics to minimize drift for PL texts
        "podatnosc": "podatność",
        "powaznosc": "poważność",
        # base tokens
        "podatność": "podatność",
        "poważność": "poważność",
        "cve": "cve",
        "cwe": "cwe",
        "cvss": "cvss",
        "atak": "atak",
        "ataki": "atak",
        "ataków": "atak",
        "wektor": "wektor",
        "wektory": "wektor",
        "łatka": "łatka",
        "latka": "łatka",
        "poprawka": "łatka",
        "aktualizacja": "łatka",
        "update": "łatka",
        "patch": "łatka",
        "eksploit": "eksploit",
        "exploit": "eksploit",
        "zagrożenie": "zagrożenie",
        "zagrozenie": "zagrożenie",
        "threat": "zagrożenie",
        "ryzyko": "ryzyko",
        "ryzyka": "ryzyko",
        "krytycznosc": "poważność",
        "krytyczność": "poważność",
    },
    # Software/Code (CODE) — unify diacritics and forms
    "code": {
        # prefer diacritics-preserving canonical forms
        "modul": "moduł",
        "blad": "błąd",
        "wyjatek": "wyjątek",
        # base tokens
        "funkcja": "funkcja",
        "metoda": "funkcja",
        "metody": "funkcja",
        "funkcje": "funkcja",
        "klasa": "klasa",
        "klasy": "klasa",
        "moduł": "moduł",
        "moduły": "moduł",
        "pakiet": "pakiet",
        "pakiety": "pakiet",
        "biblioteka": "pakiet",
        "library": "pakiet",
        "import": "import",
        "importy": "import",
        "test": "test",
        "testy": "test",
        "błąd": "błąd",
        "wyjątek": "wyjątek",
        "bug": "błąd",
        "error": "błąd",
        "exception": "wyjątek",
    },
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
        token_entropy_before=round(eb, 6),
        token_entropy_after=round(ea, 6),
        entropy_drift=round(abs(ea - eb), 6),
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
    """
    Heurystyczny dryf „encji”: użyj sygnatur tokenów odpornych na diakrytykę/mojibake.
    - liczby (≥2 cyfry) w całości,
    - pozostałe tokeny: ASCII‑fold + pierwsze 5 znaków.
    """

    def _fold(s: str) -> str:
        try:
            import unicodedata as _ud  # local import to avoid global overhead
        except Exception:  # pragma: no cover
            return s
        return "".join(ch for ch in _ud.normalize("NFKD", s) if not _ud.combining(ch))

    def _sig(text: str) -> set[str]:
        sig: set[str] = set()
        for t in _tokenize(text):
            t2 = _fold(t)
            if t2.isdigit() and len(t2) >= 2:
                sig.add(t2)
            elif len(t2) >= 5:
                sig.add(t2[:5])
        return sig

    eb = _sig(before)
    ea = _sig(after)
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


def apply_transform(
    text: str, transform: str = "identity", **params: Any
) -> tuple[str, GaugeDrift]:
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
        mapping = (
            pl_en
            if (src, dst) == ("pl", "en")
            else en_pl if (src, dst) == ("en", "pl") else {}
        )
        out = text
        for s, t in mapping.items():
            out = re.sub(rf"\b{re.escape(s)}\b", t, out, flags=re.IGNORECASE)
        return out, compute_gauge_drift(text, out)
    if transform == "jurisdiction_map":
        # Heuristic mapping marker (keeps token sets closer): annotate known legal terms
        # Idempotent: do not re-annotate tokens already marked with '§'
        keywords = ["ustawa", "rozporządzenie", "kodeks"]
        out = text
        for kw in keywords:
            # negative lookahead to avoid double annotation
            pat = rf"\b{re.escape(kw)}\b(?!§)"
            out = re.sub(pat, lambda m: m.group(0) + "§", out, flags=re.IGNORECASE)
        return out, compute_gauge_drift(text, out)
    if transform == "domain_map":
        # Canonicalize domain-specific synonyms to a stable token set
        domain = str(params.get("domain", "")).strip().lower()
        mapping = _DOMAIN_MAPS.get(domain, {})
        # include light normalization first to ensure deterministic casing/punctuation
        out = normalize_text(text, lang=str(params.get("lang", "pl")))
        for s, t in mapping.items():
            out = re.sub(rf"\b{re.escape(s)}\b", t, out, flags=re.IGNORECASE)
        return out, compute_gauge_drift(text, out)
    # Unknown transform → no‑op
    return text, compute_gauge_drift(text, text)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
