#!/usr/bin/env markdown

# CERTEUS — Plugin Supply-Chain (A8)

- Scope: `plugins/*/plugin.yaml` directories.
- Gate: `scripts/gates/plugin_supply_chain_gate.py` (report‑only by default; enforce via `ENFORCE_PLUGIN_SUPPLY=1`).

## Requirements

- SBOM: provide `sbom.json` (CycloneDX JSON) or `sbom.cdx.json` or place under `supply_chain/sbom*.json`.
- Provenance: provide `provenance.json` (in‑toto/SLSA style) or `supply_chain/provenance*.json`.
- Cosign (optional): signatures present (`*.sig`, `*.cert`) next to SBOM/provenance or in `supply_chain/`.

## Layout Example

```text
plugins/example_plugin/
  plugin.yaml
  sbom.cdx.json
  provenance.json
  # or
  supply_chain/
    sbom-1.0.0.json
    provenance-1.0.0.json
    sbom-1.0.0.json.sig
    sbom-1.0.0.json.cert
```

## Usage

- Local: `python scripts/gates/plugin_supply_chain_gate.py`
- Enforce: `ENFORCE_PLUGIN_SUPPLY=1 python scripts/gates/plugin_supply_chain_gate.py`

## CI

- The gate runs once in `ci-gates` (report‑only) and publishes a tick `out/plugin_supply_ok.txt`.
- Enforcement (if needed) should live in a dedicated security workflow or by removing `continue-on-error`.

## Notes

- Keep SBOM/provenance compatible with organization‑wide supply‑chain tooling (CycloneDX, SLSA, cosign).
- Versioning: store artifacts per version or overwrite latest; the gate is filename‑agnostic.
