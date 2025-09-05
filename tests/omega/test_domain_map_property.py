#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_domain_map_property.py             |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_domain_map_property.py             |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy property-based dla transformacji domenowych Ω‑Kernel.
EN: Property-based tests for Ω‑Kernel domain transforms.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from hypothesis import given, settings, strategies as st

from core.omega.transforms import apply_transform, compute_gauge_drift


def _idempotent(domain: str, words: list[str]) -> None:
    src = " ".join(words)
    once, _ = apply_transform(src, "domain_map", domain=domain)
    twice, _ = apply_transform(once, "domain_map", domain=domain)
    assert once == twice
    d = compute_gauge_drift(src, once)
    # Mappings nie powinny zmieniać liczby tokenów (tylko podstawienia 1:1)
    assert d.token_count_delta == 0


MED_WORDS = [
    "pacjent",
    "pacjentka",
    "pacjenci",
    "pacjentów",
    "lekarz",
    "doktor",
    "dr",
    "lek",
    "leki",
    "dawka",
    "dawki",
    "choroba",
    "choroby",
    "objaw",
    "objawy",
    "diagnoza",
    "diagnostyka",
    "terapia",
    "terapie",
]

SEC_WORDS = [
    "podatność",
    "podatnosc",
    "podatności",
    "poważność",
    "powaznosc",
    "krytyczność",
    "krytycznosc",
    "cve",
    "cwe",
    "cvss",
    "atak",
    "ataki",
    "ataków",
    "wektor",
    "wektory",
    "łatka",
    "latka",
    "patch",
    "update",
    "poprawka",
    "aktualizacja",
    "exploit",
    "eksploit",
]

CODE_WORDS = [
    "funkcja",
    "funkcje",
    "metoda",
    "metody",
    "klasa",
    "klasy",
    "moduł",
    "moduły",
    "pakiet",
    "pakiety",
    "biblioteka",
    "import",
    "importy",
    "test",
    "testy",
    "błąd",
    "blad",
    "bug",
    "error",
    "wyjątek",
    "wyjatek",
    "exception",
]


@settings(max_examples=25, deadline=None)
@given(st.lists(st.sampled_from(MED_WORDS), min_size=3, max_size=12))
def test_domain_map_med_idempotent_and_count_stable(words: list[str]) -> None:
    _idempotent("med", words)


@settings(max_examples=25, deadline=None)
@given(st.lists(st.sampled_from(SEC_WORDS), min_size=3, max_size=12))
def test_domain_map_sec_idempotent_and_count_stable(words: list[str]) -> None:
    _idempotent("sec", words)


@settings(max_examples=25, deadline=None)
@given(st.lists(st.sampled_from(CODE_WORDS), min_size=3, max_size=12))
def test_domain_map_code_idempotent_and_count_stable(words: list[str]) -> None:
    _idempotent("code", words)


def test_domain_map_sample_synonym_resolution() -> None:
    # MED
    txt, _ = apply_transform("Doktor podał leki pacjentce", "domain_map", domain="med")
    assert "lekarz" in txt and "lek" in txt and "pacjent" in txt
    # SEC
    txt, _ = apply_transform("Exploit i patch zwiększają krytycznosc", "domain_map", domain="sec")
    assert "eksploit" in txt and "łatka" in txt and "poważność" in txt
    # CODE
    txt, _ = apply_transform("Metoda w modul zgłasza exception", "domain_map", domain="code")
    assert "funkcja" in txt and "moduł" in txt and "wyjątek" in txt


# === TESTY / TESTS ===


# Mixed with noise: ensure idempotence and token count invariants hold
_NOISE_CHARS = st.characters(whitelist_categories=("Ll", "Lu"), min_codepoint=97, max_codepoint=122)
_NOISE_WORDS = st.text(alphabet=_NOISE_CHARS, min_size=3, max_size=8)


@settings(max_examples=25, deadline=None)
@given(
    st.lists(st.sampled_from(MED_WORDS), min_size=2, max_size=6),
    st.lists(_NOISE_WORDS, min_size=1, max_size=4),
)
def test_domain_map_med_idempotent_with_noise(med: list[str], noise: list[str]) -> None:
    words = med + noise
    _idempotent("med", words)


@settings(max_examples=25, deadline=None)
@given(
    st.lists(st.sampled_from(SEC_WORDS), min_size=2, max_size=6),
    st.lists(_NOISE_WORDS, min_size=1, max_size=4),
)
def test_domain_map_sec_idempotent_with_noise(sec: list[str], noise: list[str]) -> None:
    words = sec + noise
    _idempotent("sec", words)


@settings(max_examples=25, deadline=None)
@given(
    st.lists(st.sampled_from(CODE_WORDS), min_size=2, max_size=6),
    st.lists(_NOISE_WORDS, min_size=1, max_size=4),
)
def test_domain_map_code_idempotent_with_noise(code: list[str], noise: list[str]) -> None:
    words = code + noise
    _idempotent("code", words)
