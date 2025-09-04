<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/security_hardening.md                  |
| ROLE: Runbook (Security Hardening / W9).                    |
| PLIK: docs/runbooks/security_hardening.md                  |
| ROLA: Runbook (utwardzanie bezpieczeństwa / W9).            |
+-------------------------------------------------------------+
-->

# Security Hardening (W9)

Celem jest włączenie oraz kontrola bramek bezpieczeństwa w Proof Gate i CI:

- PQ‑crypto Gate (readiness/enforcement)
- TEE/Bunker Gate
- Roles Policy Gate (OPA/Rego)
- DP Budget Gate (stub z opcją wymuszenia)

## Zmienne i flagi

- `PQCRYPTO_READY` (repo var/ENV): 1/true — środowisko gotowe na PQ (raport informacyjny OK)
- `PQCRYPTO_REQUIRE` (repo var/ENV): 1/true — bramka wymaga zielonego statusu PQ (w przeciwnym razie fail)
- `BUNKER` / `PROOFGATE_BUNKER`: 1/true — profil TEE/Bunker (nagłówki RA; enforcement wg ról)
- `FINE_GRAINED_ROLES`: 1/true — włącza enforcement ról (OPA) w ProofGate smoke/gate
- `STRICT_DP_BUDGET`: 1/true — wymusza DP Budget Gate (brak/za wysoki `dp_epsilon` ⇒ fail)

## Jak działa w Proof Gate

Workflow: `.github/workflows/proof-gate.yml`

- PQ‑crypto Gate:
  - Krok: „PQ-crypto Gate (readiness)”: `scripts/gates/pqcrypto_gate.py`
  - Flagi: `PQCRYPTO_READY`, `PQCRYPTO_REQUIRE`
- Bunker Gate:
  - Krok: „Security Bunker Gate (TEE profile)”: `scripts/gates/security_bunker_gate.py`
  - Flagi: `BUNKER`, `PROOFGATE_BUNKER`
- Roles Policy Gate:
  - Krok: `scripts/gates/roles_policy_gate.py` (OPA proxy, Governance pack)
  - Flagi: `FINE_GRAINED_ROLES`
- DP Budget Gate:
  - Krok: `scripts/gates/dp_budget_gate.py`
  - Flaga: `STRICT_DP_BUDGET`

Boundary‑Rebuild (delta_bits==0) jest uruchamiane warunkowo, gdy dostępne są klucze `PCO_JWKS_B64URL` (walidacja Merkle/Ed25519).

## Lokalny dry‑run

Przykład (PowerShell):

```
$env:PQCRYPTO_READY='1'
$env:PQCRYPTO_REQUIRE='0'
$env:BUNKER='0'
$env:FINE_GRAINED_ROLES='0'
$env:STRICT_DP_BUDGET='0'
uv run python scripts/gates/pqcrypto_gate.py
uv run python scripts/gates/security_bunker_gate.py
uv run python scripts/gates/roles_policy_gate.py < NUL
uv run python scripts/gates/dp_budget_gate.py < NUL
```

## Troubleshooting

- PQ‑crypto Gate: ustaw `PQCRYPTO_READY=1` aby oznaczyć gotowość; w trybie wymagającym (`PQCRYPTO_REQUIRE=1`) gate musi przejść.
- Roles Gate: upewnij się, że Governance Pack jest spójny (`scripts/validate_governance_consistency.py`).
- Bunker Gate: brak RA/TEE ⇒ informacyjny; ustaw `BUNKER=1` aby wymusić profil.
- DP Budget Gate: brak `dp_epsilon` lub wartość > 1.0 ⇒ fail w trybie `STRICT_DP_BUDGET=1`.

## Artefakty/raporty

- Proof Gate publikuje w PR ticki per krok oraz artefakty (SBOM, provenance, OpenAPI). Dodatkowo UI Demos workflow wrzuca raporty smoke’ów do artefaktów.

