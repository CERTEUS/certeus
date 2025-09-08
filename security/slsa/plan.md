# SLSA-3 Plan (Draft)

- Source integrity: branch protections, required checks (`ci-gates`, `smoke`).
- Build integrity: GitHub-hosted runners, provenance attestations (SBOM + in-toto-like JSON).
- Signing: cosign keyless in `release.yml` (SBOM/provenance).
- Reproducibility: pin deps where feasible; document seeds and environment.
- Verification: policy-controlled enforcement in supply-chain gate (enforce on tags).

Next steps:
- Harden builders; attest image digests; verify prior to deploy.
- Record provenance in a dedicated public log (append-only).

