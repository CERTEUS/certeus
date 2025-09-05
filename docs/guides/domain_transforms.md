# Ω‑Kernel — Transformacje domenowe i inwarianty (Gauge)

PL: Specyfikacja lekkich transformacji tekstu (lang/jur/ontology) oraz inwariantów Gauge w wersji MVP.

EN: Specification of lightweight text transformations (lang/jur/ontology) and Gauge invariants, MVP.

## Zakres / Scope

- Normalizacja językowa (whitespace/quotes/dashes/case) — `normalize`.
- Mapowanie jurysdykcyjne (PL→EN term base) — `jurisdiction_map`.
- Inwarianty Gauge — delta liczby tokenów, Jaccard drift na zbiorach tokenów.

## Inwarianty / Invariants

- `token_count_delta` — |tokens(after) − tokens(before)| ≤ T (MVP: T=1 dla `normalize`).
- `jaccard_drift` — 1 − |A∩B|/|A∪B|; dla `normalize` ≤ 0.05, dla `jurisdiction_map` ≤ 0.50.

## API (Python)

- `core.omega.transforms.normalize_text(text, lang='pl') -> str`
- `core.omega.transforms.compute_gauge_drift(before, after) -> GaugeDrift`
- `core.omega.transforms.apply_transform(text, transform: str, **params) -> (str, GaugeDrift)`

## Testy / Tests

- `tests/omega/test_transforms_invariants.py` — testy inwariantów (identity/no‑drift, normalize/low‑drift, jurisdiction_map/bounded).

## Uwagi / Notes

- MVP nie zmienia składni/semantyki zdań; przyszłe wersje rozszerzą mappingi i mierniki (np. NER‑based invariants, entropy drift).
- Integracja z Gauge‑Gate: możliwe wykorzystanie `compute_gauge_drift` jako wejścia do `scripts/gates/compute_gauge_drift.py`.
