# CERTEUS Bench — Methodology (v0.1)

- Determinism: fixed seeds, stable RNG, cold vs warm-up separated.
- Metrics: API p95 for (/health, /openapi.json, /metrics); optional domain metrics.
- Artifacts: `out/bench.json` (current) and `ci/bench.json` (baseline for trend).
- Repro: `python bench/run.py --iters 10 --out out/bench.json`.

