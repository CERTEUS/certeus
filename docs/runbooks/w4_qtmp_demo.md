<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/w4_qtmp_demo.md                        |
| ROLE: Docs runbook.                                          |
| PLIK: docs/runbooks/w4_qtmp_demo.md                        |
| ROLA: Runbook dokumentacji.                                  |
+-------------------------------------------------------------+
-->

# W4 — QTMP Demo (pomiar, sekwencja, dekoherencja)

## Cel
- Zainicjalizować sprawę (basis), wykonać pomiary L→T i T→L, włączyć dekoherencję i zweryfikować wpisy w Ledger.

## Kroki lokalne
- `uv run --group dev python scripts/smokes/w4_qtmp_demo.py`
  - `POST /v1/qtm/init_case`
  - `POST /v1/qtm/measure {operator: LT}` i `{operator: TL}`
  - `POST /v1/qtm/decoherence {channel: dephasing, gamma: 0.2}`
  - `GET /v1/ledger/{case}/records` — liczba wpisów (sequence + collapse_event)

## DOD
- PCO headers: `X-CERTEUS-PCO-qtm.collapse_event`, `X-CERTEUS-PCO-qtm.predistribution[]` (gdy dostępne)
- `uncertainty_bound.L_T` zależne od CFE `kappa_max` (most CFE↔QTMP)
- Collapse logowany do Ledger (hash sequence i collapse_event)

