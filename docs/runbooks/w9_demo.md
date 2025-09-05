#!/usr/bin/env markdown

# CERTEUS — Runbook: W9 Security Hardening

## Gates

- Roles Policy Gate (OPA proxy skeleton): `scripts/gates/roles_policy_gate.py`
- Security Bunker Gate: `scripts/gates/security_bunker_gate.py`
- PQ‑Crypto Gate (informational): `scripts/gates/pqcrypto_gate.py`

## Demo

- `python scripts/demos/run_w9_demo.py` → zapisuje `reports/w9_demo.json` i uruchamia trzy bramki:
  - Roles: OK (AFV/publish) i FAIL (XXX/merge),
  - Bunker: BUNKER=off (OK) i BUNKER=on z attestacją (OK),
  - PQ‑crypto: status w `out/pqcrypto.txt`.

## Testy lokalne

- Roles: `pytest -q tests/gates/test_roles_policy_gate.py`
- Bunker: `pytest -q tests/gates/test_security_bunker_gate.py`
- PQ‑crypto: `pytest -q tests/gates/test_pqcrypto_gate_smoke.py`

