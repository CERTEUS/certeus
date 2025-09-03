#!/usr/bin/env markdown

# SOC 2 (Security/Availability/Confidentiality) Checklist (CERTEUS)

- Security: Proof-Only I/O (middleware), OPA/Rego roles gate, Bunker gate
- Availability: SLO Smoke (p95 + error_rate), DR-Drill (Boundary)
- Confidentiality: Redaction Gate, zero-PII public payload policy

Evidence pointers:
- scripts/gates/security_bunker_gate.py, roles_policy_gate.py, redaction_gate.py
- scripts/slo_gate/*, scripts/dr/*
- policies/pco/policy_pack.yaml (redaction rules)

