#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/dp_policies.md                          |
# | ROLE: Runbook — Data Protection Policies (OPA/Rego)         |
# +-------------------------------------------------------------+

## Cel (W5 — A8)
- Opracować i testować polityki DP/ZK w OPA/Rego.
- W CI uruchomić `dp_policy_gate.py` (report‑only; enforcement przez `DP_POLICY_ENFORCE=1`).

## Pliki
- `policies/security/dp.rego` — logika DP (PII → wymaga redakcji/purpose).
- `policies/security/dp_test.rego` — testy jednostkowe OPA.
- `scripts/gates/dp_policy_gate.py` — gate (CLI `opa` lub Docker fallback).

## Lokalnie
1) OPA CLI (zalecane): `brew install opa` lub pobierz binarkę.
2) Testy: `opa test policies/security`.
3) Próbki: `python scripts/gates/dp_policy_gate.py` → `out/dp_policy_report.json`.

## CI (ci-gates.yml)
- Krok „DP Policy Gate (OPA/Rego)” uruchamia testy, zapisuje raport i dodaje sekcję do PR komentarza.
- Enforcement można włączyć przez `DP_POLICY_ENFORCE=1` (na razie report‑only).

