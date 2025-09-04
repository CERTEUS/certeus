<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/w5_operator_composer.md                |
| ROLE: Docs runbook.                                          |
| PLIK: docs/runbooks/w5_operator_composer.md                |
| ROLA: Runbook dokumentacji.                                  |
+-------------------------------------------------------------+
-->

# W5 — Operator Composer & Presets (Runbook)

## Cel
- Zapisać preset operatora dla sprawy i zweryfikować, że `/v1/qtm/measure` używa presetu (operator w PCO nagłówku).

## Kroki lokalne
- `uv run --group dev python scripts/smokes/w5_operator_composer_demo.py`
  - `POST /v1/qtm/preset {case, operator}`
  - `POST /v1/qtm/measure {operator: L, source: <case>}` — PCO header zawiera `operator=T` (preset)

## DOD
- PCO headers: `X-CERTEUS-PCO-qtm.collapse_event` zawiera `operator` i `verdict`.
- Preset przechowywany w `data/qtm_presets.json` (stub, idempotentny zapis/odczyt).

