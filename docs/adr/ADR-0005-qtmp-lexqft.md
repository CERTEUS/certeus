#!/usr/bin/env markdown

# ADR-0005: QTMP/lexqft Contracts and Invariants

- Status: Accepted
- Date: 2025-09-02

Context

- QTMP measurement API and lexqft coverage/tunneling expose domain contracts used by gates and smokes.

Decision

- QTMP: expose init_case/measure/measure_sequence/expectation/state with PCO headers (collapse, predistribution, priorities).
- LexQFT: expose coverage/coverage_state/tunnel with Prometheus metrics and persistence of coverage state.
- Tests enforce invariants (probability bounds, UB range) and smoke flows.

Consequences

- Enables Path-Coverage-Gate and perf/SLO smokes to rely on deterministic contracts.

References

- services/api_gateway/routers/qtm.py, routers/lexqft.py
- tests/services/test_qtm_invariants.py, tests/smokes/lexqft_smoke.py
