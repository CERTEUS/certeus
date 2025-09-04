#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/kms_rotation.md                         |
# | ROLE: Runbook — Key rotation / KMS                          |
# +-------------------------------------------------------------+

## Cel (W9 — A8)
- Opisać i kontrolować rotację kluczy (KMS/HSM lub lokalne dev keys).
- Raportować obecność artefaktów polityki w CI.

## Artefakty (dev)
- `security/keys/metadata.json` z polami `current`, `previous`, `algo`.
- Alternatywnie: `security/keys/current.*` i `security/keys/prev.*`.

## Gate (report-only)
- `scripts/security/kms_rotation_gate.py` — zapis `out/kms_rotation.json`.
- PR komentarz: pokazuje tryb (metadata/files) i obecność.

