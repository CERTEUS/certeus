#!/usr/bin/env markdown

# CERTEUS — Runbook: W3/W4 Demo

Cel: szybkie uruchomienie demo dla tygodni 3 i 4.

## W3 — Geodesic + Lock → Publish

1) Uruchom skrypt (in‑proc):

   - `python scripts/demos/run_w3_demo.py`

2) Oczekiwane efekty:

   - `reports/w3_demo.json` z polami: `geodesic_action`, `locked`, `status` (z ProofGate),
   - Zapis do Ledger (PCO_PUBLISH) dla `case=LEX-DEMO-W3`.

3) Cockpit (opcjonalnie):

   - Otwórz `clients/web/public/geometry.html` w przeglądarce lokalnej, sprawdź heatmapę Ricciego i `observed_at`.

## W4 — QTMP (pomiar, nieoznaczoność)

1) Uruchom skrypt (in‑proc):

   - `python scripts/demos/run_w4_demo.py`

2) Oczekiwane efekty:

   - `reports/w4_demo.json` z sekwencjami L→T oraz T→L i różnicą prawdopodobieństw `diff_last`.

3) Cockpit Quantum (`clients/web/public/qtm.html`):

   - `Init case`, następnie `Measure L→T` lub `T→L`,
   - Ustaw `Decoherence: dephasing`,
   - `Build heatmap` — 5×5 macierz komutatorów W/I/C/L/T.

## Dodatkowo

- W2/W3/W4 demom towarzyszą raporty SBOM i perf:
  - `python scripts/supply_chain/generate_sbom.py` → `reports/sbom.json`,
  - `python scripts/demos/run_w2_demo.py` → `out/perf_bench.json`.

