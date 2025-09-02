#!/usr/bin/env markdown
# CERTEUS — WORKLOG

Zbiorczy dziennik prac — krótkie wpisy po każdej zmianie (gałąź, data, skrót).

- 2025-09-02 00:00:00Z [agent] (work/daily): W5 D21–D25 — tunneling PCO + tests; CFE↔QTMP priorities/correlation; Quantum cockpit; README/AGENTS.
  - /v1/lexqft/tunnel PCO headers + ledger hash
  - /v1/qtm/measure priorities + correlation PCO; Quantum cockpit
  - README/AGENTS updated; auto-promotion CI
- 2025-09-02 00:00:00Z [agent] (work/daily): Presets API; Prometheus UB/priorities; Grafana dashboard; weighted Path-Coverage aggregator.
  - /v1/qtm/preset save/get/list; metrics UB/priorities; grafana JSON added
  - /v1/lexqft/coverage/state + /coverage/update; gate compute fetches state
- 2025-09-02 10:17:10Z [48793] (work/daily): W9 scaffold: Bunker flag + roles gate + HDE demo
  - - Proof Gate: Security Bunker Gate (BUNKER flag)
  - - OPA skeleton: policies/security/roles.rego
  - - Gate: scripts/gates/roles_policy_gate.py
  - - README: demo HDE wygrany case
  - - CI: proof-gate + promote-daily-to-main (WORKLOG pre-merge)
