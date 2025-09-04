<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/w7_finenith_demo.md                    |
| ROLE: Docs runbook.                                          |
| PLIK: docs/runbooks/w7_finenith_demo.md                    |
| ROLA: Runbook dokumentacji.                                  |
+-------------------------------------------------------------+
-->

# W7 — FINENITH v0.1 (R/S + Entanglement MI)

## Cel
- Zademonstrować operatory R/S (commutator_norm) i entanglement MI.

## Kroki lokalne
- `uv run --group dev python scripts/smokes/w7_fin_demo.py`
  - `POST /v1/fin/alpha/operators_rs` → `R`, `S`, `commutator_norm`
  - `POST /v1/fin/alpha/entanglement/mi` → `top` (para, mi)

## Polityki (OPA)
- `policies/finance/risk.rego` — deny gdy `R > risk_max`.
- `policies/finance/entanglement.rego` — deny gdy `mi > mi_max`.

