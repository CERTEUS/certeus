#!/usr/bin/env markdown

# ISO 27001 Checklist (CERTEUS)

- A.5 Policies: policies/pco/policy_pack.yaml; governance_pack.v0.1.yaml
- A.8 Asset Management: asset-guard workflow; SBOM (supply-chain.yml)
- A.12 Operations Security: ci-gates, ProofGate gates, redaction gate
- A.14 System Acquisition/Development: Premium Style Gate, tests, SLO/Perf gates
- A.18 Compliance: DPIA (docs/compliance/dpia.md), redaction, PNIP validation

Evidence pointers:
- Workflows: .github/workflows/*
- Logs/Artifacts: ci-gates outputs (out/*), perf-bench artifact
- Policies: policies/*

