#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/spiffe_identities.md                    |
# | ROLE: Runbook — SPIFFE/SPIRE identities                     |
# +-------------------------------------------------------------+

## Cel (W8 — A8)
- Przygotować tożsamości SPIFFE/SPIRE dla usług (trust domain, SVID).
- Docelowo QUIC/Noise transport (PoC) + SPIFFE ID → mTLS policy.

## Artefakty
- `infra/spiffe/svid.json` — lokalny SVID (dev/CI; nie zawiera sekretów).
- ENV: `SPIFFE_ID`, `TRUST_DOMAIN` — fallback.

## Gate (report-only)
- `scripts/security/spiffe_identity_gate.py` — zapisuje `out/spiffe_report.json` z informacją o stanie.
- Włącza sekcję w PR komentarzu (present/missing).

