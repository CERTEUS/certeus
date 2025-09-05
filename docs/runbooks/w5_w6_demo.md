#!/usr/bin/env markdown

# CERTEUS — Runbook: W5/W6 Demo

## W5 — LexQFT + Path‑Coverage

1) Tunelowanie i coverage z progiem Gate:
   - `python scripts/demos/run_w5_demo.py`
   - Raport: `reports/w5_demo.json`
   - Gate: `scripts/gates/path_coverage_gate.py --min-gamma 0.90 --max-uncaptured 0.10 --input out/path_cov_demo.json`

2) UI (opcjonalnie): `clients/web/public/geometry.html` (lensing) i `clients/web/public/qtm.html` (LT/TL).

## W6 — Devices v0.1

1) Demo urządzeń:
   - `python scripts/demos/run_w6_demo.py`
   - Raport: `reports/w6_demo.json`

2) UI urządzeń:
   - Otwórz `clients/web/public/devices.html`, użyj formularzy dla HDE/Q‑Oracle/Entangler/Chronosync.

