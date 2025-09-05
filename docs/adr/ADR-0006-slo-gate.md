#!/usr/bin/env markdown

# ADR-0006: SLO Gate (p95 + Error Rate)

- Status: Accepted
- Date: 2025-09-02

Context

- We require stable latency and reliability, measured in-proc during CI.

Decision

- SLO Smoke measures response times and error rate and checks thresholds (p95 ≤ 300 ms, error_rate ≤ 1%).
- Gate outputs markers (out/slo_ok.txt) and participates in ci-gates summary.

Consequences

- Early detection of performance or reliability regressions in CI, independent of perf bench.

References

- scripts/slo_gate/measure_api.py, scripts/slo_gate/check_slo.py
- .github/workflows/ci-gates.yml (SLO Smoke)
