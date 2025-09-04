#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/licensing_gate.md                       |
# | ROLE: Runbook — Licensing Gate for plugins                   |
# +-------------------------------------------------------------+

## Cel (W13 — A8)
- Wymusić minimalne metadane i licencję dla pluginów/packs.
- W CI raportować braki i niedozwolone licencje.

## Gate
- `scripts/gates/license_gate.py` — skanuje `plugins/*/plugin.yaml`.
- Wymagane pola: `name`, `module`, `version`, `license`.
- Allowlista: `policies/security/licenses.allowlist.json`.
- Raport: `out/license_report.json` (report-only; można włączyć enforcement przez `LICENSE_POLICY_ENFORCE=1`).

## Lokalnie
```
python scripts/gates/license_gate.py
cat out/license_report.json
```

