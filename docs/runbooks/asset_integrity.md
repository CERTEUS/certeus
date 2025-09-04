#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/asset_integrity.md                      |
# | ROLE: Runbook — Asset Integrity Gate (PCO public)           |
# +-------------------------------------------------------------+

## Cel (W7 — A8)
- Zapewnić minimalną integralność opublikowanych PCO (public payloads).
- Automatyczny przegląd `data/public_pco/*.json` w CI.

## Gate
- Skrypt: `scripts/gates/asset_integrity_gate.py`.
- Weryfikuje: `spec`, `claims[]`, `proof.root`.
- Raport: `out/asset_integrity.json`; OK: `out/asset_ok.txt`.
- Enforcement (FAIL) przez `ASSET_INTEGRITY_ENFORCE=1`.

## Lokalnie
```
python scripts/gates/asset_integrity_gate.py
cat out/asset_integrity.json
```

