#!/usr/bin/env markdown

# ADR-0002: PNIP Validation on Ingress

- Status: Accepted
- Date: 2025-09-02

Context
- Proof-Native Input Profile (PNIP) defines minimal headers/body required for auditable ingestion: document hash, jurisdiction, policy pack id.

Decision
- Validate PNIP in `/defx/reason` and `/v1/ledger/record-input` with optional strict mode (`STRICT_PNIP=1`).
- On invalid PNIP (strict): return 400 with PCO-style error document.

Consequences
- Stricter ingress, explicit error contracts, tests enforce behavior.

References
- services/api_gateway/pnip.py
- tests/services/test_pnip_strict.py, tests/services/test_pnip_property.py

