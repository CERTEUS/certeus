CERTEUS Supply-Chain Runbook

Scope
- Repository SBOM/provenance (repo root)
- Plugins SBOM/provenance (+ optional cosign signatures)

Enforcement
- CI step: `.github/workflows/ci-gates.yml` → "Supply-Chain Enforce (required)"
- Env toggles:
  - `SUPPLY_CHAIN_ENFORCE=1` → enforce SBOM/provenance at repo and plugin level (deny-by-default)
  - `REQUIRE_COSIGN=1` → additionally require cosign signatures for plugins (`*.sig`/`*.cert`)

Expected artifacts
- Root: `sbom.json` (or `artifact.json`)
- Plugin directory (e.g., `plugins/foo`):
  - `plugin.yaml` (manifest)
  - SBOM: `sbom.json` or `sbom.cdx.json` or files under `supply_chain/sbom*.json`
  - Provenance: `provenance.json` or files under `supply_chain/provenance*.json`
  - Cosign (optional unless REQUIRED): `*.sig`, `*.cert` (at plugin root or `supply_chain/`)

Local development
- To run gate locally: `python scripts/gates/supply_chain_enforce.py`
- To enforce: `SUPPLY_CHAIN_ENFORCE=1 python scripts/gates/supply_chain_enforce.py`
- To require cosign: `REQUIRE_COSIGN=1 SUPPLY_CHAIN_ENFORCE=1 python scripts/gates/supply_chain_enforce.py`

Notes
- The report is written to `out/supply_chain_enforce.json` in CI.
- Non-enforcing mode prints INFO/WARN and exits 0 to avoid blocking initial PRs.

