#!/usr/bin/env markdown

# CI Enforce Flags (A8)

Krótki runbook dla maintainerów — jak włączyć egzekwowanie wybranych bramek (domyślnie report‑only):

## Flagi i bramki

- `ENFORCE_MARKETPLACE_POLICY=1`
  - Gate: `scripts/gates/marketplace_policy_gate.py`
  - Efekt: brak `name`/złe `version`/niedozwolona `license` stanie się błędem (exit 1).

- `ENFORCE_PLUGIN_SUPPLY=1`
  - Gate: `scripts/gates/plugin_supply_chain_gate.py`
  - Efekt: brak SBOM/provenance w `plugins/*` stanie się błędem (exit 1).

- `ENFORCE_COMPLIANCE_MAPPING=1`
  - Gate: `scripts/gates/compliance_mapping_gate.py`
  - Efekt: brak wymaganych dokumentów DPIA/ISO27001/SOC2 stanie się błędem (exit 1).

## Jak użyć w GitHub Actions

Przykład (krok w dedykowanym workflow blokującym):

```yaml
jobs:
  security-gates:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with:
          python-version: '3.11'
      - run: |
          python -m pip install -U pip wheel setuptools
          python -m pip install -e .
      - name: Enforce Marketplace & Plugin supply-chain
        env:
          ENFORCE_MARKETPLACE_POLICY: '1'
          ENFORCE_PLUGIN_SUPPLY: '1'
        run: |
          python scripts/gates/marketplace_policy_gate.py
          python scripts/gates/plugin_supply_chain_gate.py
```

Uwaga: w `ci-gates.yml` bramki pozostają w trybie report‑only dla szybkości i niskiej inwazyjności; egzekwowanie przenieś do workflow bezpieczeństwa lub PR‑gate’ów wymagających.

