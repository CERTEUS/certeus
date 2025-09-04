<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/w6_devices_demo.md                     |
| ROLE: Docs runbook.                                          |
| PLIK: docs/runbooks/w6_devices_demo.md                     |
| ROLA: Runbook dokumentacji.                                  |
+-------------------------------------------------------------+
-->

# W6 — Devices v0.1 (HDE/Q-Oracle/Entangle/Chronosync)

## Cel
- Zademonstrować urządzenia: HDE plan, Q-Oracle expectation, Entangler, Chronosync reconcile.

## Kroki lokalne
- `uv run --group dev python scripts/smokes/w6_devices_demo.py`
  - `POST /v1/devices/horizon_drive/plan` — koszt, expected_kappa, alternatywy.
  - `POST /v1/devices/qoracle/expectation` — optimum (choice), payoff, rozkład.
  - `POST /v1/devices/entangle` — certificate header (PCO), achieved_negativity.
  - `POST /v1/devices/chronosync/reconcile` — reconciled + szkic klauzul.

## PR Summary (snapshots)
- HDE: `cost_tokens`, `expected_kappa` (linie w PR).
- Q-Oracle: `payoff`, `optimum.choice` (linie w PR).
- Entangler: `achieved_negativity` (linia w PR).
- Chronosync: `reconciled` (linia w PR).

