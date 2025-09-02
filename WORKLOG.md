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
- 2025-09-02 10:20:42Z [48793] (work/daily): W9: README flags + roles.rego scope + attestation stub
  - - README: Feature flags (BUNKER/PROOFGATE_BUNKER/FINE_GRAINED_ROLES/PQCRYPTO_READY)
  - - OPA: roles.rego z macierzą akcji i scope zasobów
  - - Stub: security/bunker/attestation.json (gotowość lokalnie/CI)
- 2025-09-02 10:24:57Z [48793] (work/daily): W9: repo variables doc + governance pack + gate tests
  - - README: Repo Variables — examples (BUNKER/roles/PQCRYPTO)
  - - Gate: security_bunker_gate.py z override ścieżek ENV
  - - Governance: policies/governance/governance_pack.v0.1.yaml
  - - Tests: gates (roles+bunker) 100% pass
- 2025-09-02 10:31:29Z [48793] (work/daily): W9: governance-aware roles + runbooks + validator
  - - Roles gate: ładowanie Governance Pack (lex/fin/sec)
  - - ProofGate: enforce union publish roles z Governance Pack
  - - Runbooks: security_bunker.md, roles_governance.md
  - - Validator: scripts/validate_governance_consistency.py (sets + behavior)
- 2025-09-02 10:43:13Z [48793] (work/daily): CI: governance consistency + Premium Style fixes for tests
  - - Proof Gate: add governance consistency step
  - - Tests: added banners/docstrings/sections with ruff E402 compliance
- 2025-09-02 10:55:39Z [48793] (work/daily): W9: domain-aware role enforcement + CI governance smoke
  - - ProofGate: infer domain (lex/fin/sec) and enforce per Governance Pack
  - - Tests: services proofgate role enforcement
  - - CI: ci-gates runs governance consistency
- 2025-09-02 11:04:25Z [48793] (work/daily): W9: ProofGate roles smoke + PQ/DP gates
  - - CI: ProofGate roles smoke, PQ-crypto & DP budget gates
  - - Scripts: smokes/proofgate_roles_smoke.py, gates/pqcrypto_gate.py, gates/dp_budget_gate.py
  - - README: dodane flagi PQCRYPTO_REQUIRE i STRICT_DP_BUDGET
