#!/usr/bin/env markdown

# ADR-0004: PII Redaction Gate

- Status: Accepted
- Date: 2025-09-02

Context

- Public payloads must contain zero PII; policy-driven redaction is required before publish or demo flows.

Decision

- Provide `scripts/gates/redaction_gate.py` consuming JSON (stdin or file) and policy pack regexes.
- `STRICT_REDACTION=1` turns detections into failures.

Consequences

- CLI-friendly for CI and local checks; tests verify strict and non-strict modes.

References

- policies/pco/policy_pack.yaml (redaction.pii_patterns)
- tests/gates/test_redaction_gate_cli.py
