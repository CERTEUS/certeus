#!/usr/bin/env markdown

# CERTEUS — Marketplace Policies (A8)

- Scope: `plugins/*/plugin.yaml` manifests.
- Gate: `scripts/gates/marketplace_policy_gate.py` (report‑only by default; enforce via `ENFORCE_MARKETPLACE_POLICY=1`).

## Requirements

- Name: `name` is required and must be non‑empty.
- SemVer: `version` must follow `MAJOR.MINOR.PATCH[-pre][+build]`.
- License: if present, must be one of: `MIT`, `Apache-2.0`, `BSD-2-Clause`, `BSD-3-Clause`.
- Signature: optional `signature` field recommended; basic sanity (length ≥ 40 chars).

## Usage

- Local: `python scripts/gates/marketplace_policy_gate.py`
- Enforce: `ENFORCE_MARKETPLACE_POLICY=1 python scripts/gates/marketplace_policy_gate.py`

## CI

- The gate runs once in `ci-gates` (report‑only) and publishes a tick file `out/marketplace_ok.txt` when successful.
- Optionally keep coverage via smoke test `tests/policies/test_marketplace_policy_gate.py`.

## Notes

- Gate is conservative and non‑intrusive; it will not fail CI unless explicitly enforced.
- For richer checks (SBOM, provenance, cosign), use existing supply‑chain workflows and extend as needed.
