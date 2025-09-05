# CERTEUS — Ω‑Kernel: `domain_map` (MED/SEC/CODE)

"""
PL: Canonicalizacja domenowa niskiego dryfu (1→1) dla słownictwa MED/SEC/CODE.
EN: Low‑drift (1→1) domain canonicalization for MED/SEC/CODE vocabulary.
"""

## Założenia

- Substytucje 1→1 na granicach słów, bez usuwania/dodawania tokenów.
- Idempotencja: wielokrotne zastosowanie nie zmienia wyniku.
- Kanon w języku PL (z diakrytyką tam, gdzie to stabilizuje zbiory tokenów).
- Celem jest stabilność metryk Gauge, nie „twarda” translacja semantyczna.

## Użycie (Python)

```python
from core.omega.transforms import apply_transform

txt = "Doktor podał leki pacjentce"
out, drift = apply_transform(txt, "domain_map", domain="med")
assert out  # "lekarz" i "lek" i "pacjent" w kanonie
```

Dozwolone domeny: `med`, `sec`, `code`.

## Raportowanie w bramce (compute_gauge_drift)

Skrypt `scripts/gates/compute_gauge_drift.py` obsługuje tryb domenowy:

```bash
python scripts/gates/compute_gauge_drift.py \
  --out out/gauge.json \
  --before-file before.txt --after-file after.txt \
  --domain med \
  --max-jaccard-mapped 0.3 --max-entropy-mapped 0.5 --max-entity-jaccard-mapped 0.6
```

Wynik zawiera sekcję `omega_mapped` z metrykami po `domain_map`.

- Progi `--max-*-mapped` (lub ENV: `OMEGA_MAX_JACCARD_MAPPED`, `OMEGA_MAX_ENTROPY_MAPPED`, `OMEGA_MAX_ENTITY_DRIFT_MAPPED`) są raportowe.
- Wymuszenie porażki wyłącznie z `ENFORCE_OMEGA_MAPPED=1` (domyślnie report‑only).

## Inwarianty (testowane)

- Idempotencja: `domain_map(domain, text)` zastosowany 2× daje identyczny wynik.
- Nie zmienia liczby tokenów (operacje 1→1, granice słów).
- Bounded drift w scenariuszach przykładowych (testy jednostkowe).

## Rozszerzanie słowników

- Dodawaj tylko równania 1→1, preferuj formy kanoniczne z PL diakrytyką.
- Unikaj „agresywnej” normalizacji, która zmieniłaby liczbę tokenów.
- Każdy dodatek powinien być pokryty property‑testami (idempotencja, token_count==0).

