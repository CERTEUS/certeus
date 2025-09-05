# Roles & Governance — Runbook

Cel: kontrola akcji (publish/merge/…) per rola i domena zgodnie z Governance Pack.

Włączenie

- Ustaw `FINE_GRAINED_ROLES=1` (repo variable lub ENV w runtime) — ProofGate egzekwuje rolę dla `publish/conditional`.
- Opcjonalnie `GOV_PACK` (ścieżka do YAML) oraz `GOV_DOMAIN` (domyślna domena) dla bramki ról.

Pliki

- Polityka OPA (szkielet): `policies/security/roles.rego`
- Governance Pack: `policies/governance/governance_pack.v0.1.yaml`
- Bramka: `scripts/gates/roles_policy_gate.py` (ładuje pack, fallback do szkieletu)

Walidacja

```
python scripts/validate_governance_consistency.py \
  --pack policies/governance/governance_pack.v0.1.yaml \
  --rego policies/security/roles.rego
```

Sprawdza zbiory ról/akcji oraz zachowanie bramki ról względem packa.

Przykłady

```
echo '{"user":{"role":"AFV"},"action":"publish","resource":{"kind":"pco","scope":"lex"}}' \
  | python scripts/gates/roles_policy_gate.py

echo '{"user":{"role":"ATC"},"action":"manage_keys","resource":{"kind":"keys","scope":"sec"}}' \
  | python scripts/gates/roles_policy_gate.py
```
