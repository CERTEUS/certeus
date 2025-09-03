#!/usr/bin/env markdown

# ADR-0003: CI Gates and Perf Regression Guard

- Status: Accepted
- Date: 2025-09-02

Context
- The project uses multiple gates (style, lint, tests, perf, SLO, governance, supply-chain) as quality bars.
- Perf can regress subtly despite meeting absolute p95 threshold.

Decision
- Maintain `ci-gates` workflow with deterministic smokes and checks.
- Add Perf Regression Gate: fail if worst p95 degrades by >20% vs previous run (if baseline available).

Consequences
- CI fails early on performance regressions even under threshold.
- Baseline taken from `ci-status` branch artifact when present.

References
- .github/workflows/ci-gates.yml (Perf Smoke + Regression Gate)

