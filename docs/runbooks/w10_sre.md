#!/usr/bin/env markdown

# CERTEUS — Runbook: W10 Observability & SRE

## Zależności

- OTel (opcjonalnie): `OTEL_ENABLED=1`, mock OTLP: `scripts/otel/mock_otlp.py`.
- Metryki Prometheus: endpoint `/metrics`; dashboard: `observability/grafana/certeus-sre-dashboard.json`.

## SLO / Perf

- Pomiar SLO (in‑proc, bez serwera):
  - `python scripts/slo_gate/measure_api.py` → `out/slo.json`
  - `python scripts/slo_gate/check_slo.py` (progi `SLO_MAX_P95_MS`, `SLO_MAX_ERROR_RATE`)
- Quick perf bench (p95):
  - `python scripts/perf/quick_bench.py --iters 10 --p95-max-ms 300 --out out/perf_bench.json`

## Demo

- `python scripts/demos/run_w10_demo.py` → `reports/w10_demo.json`
  - Uruchamia SLO measure+check i perf bench, zbiera statusy.

## Smoki

- `/metrics`: `python scripts/smokes/metrics_smoke.py`
- `/openapi.json`: `python scripts/smokes/openapi_smoke.py`

