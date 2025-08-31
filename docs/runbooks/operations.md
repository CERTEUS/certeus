# Operations Runbook (MVP)

- API Gateway (DEV):
  - `python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`
  - Env:
    - `STRICT_PROOF_ONLY=1` (opcjonalnie)
    - `PROOF_BUNDLE_DIR=./data/public_pco`
    - `DEFAULT_BUDGET_TOKENS=10`
    - Keys: `ED25519_PRIVKEY_PEM` + `ED25519_PUBKEY_B64URL` (lub KEYS_BACKEND=vault)

- ProofGate:
  - Embedded in-process via `services.proofgate.app`; for standalone: `uvicorn services.proofgate.app:app --port 8085`

- Ledger API:
  - GET/POST under `/v1/ledger/*` (see OpenAPI)
  - Optional schema validation of receipts: `LEDGER_VALIDATE_SCHEMA=1`

- Metrics (Prometheus):
  - Scrape `http://<gateway>/metrics`
  - Load rules: `observability/prometheus/recording_rules.yml`
  - Alerts/SLO Gate: `monitoring/slo/slo_gate.yml`

- Grafana:
  - Import dashboard JSON: `observability/grafana/certeus-slo-dashboard.json`

- Key Management:
  - ENV/files: `ED25519_PRIVKEY_PEM`, `ED25519_PUBKEY_B64URL` (`docs/security/key_management.md`)
  - Vault: `KEYS_BACKEND=vault`, `VAULT_ADDR`, `VAULT_TOKEN`, `VAULT_SECRET_PATH`

- Supply Chain (CI):
  - Workflow: `.github/workflows/supply-chain.yml` (SBOM/Trivy/Cosign/SLSA)

- Troubleshooting:
  - High `certeus_abstain_rate`: inspect proof verification failures, budget tokens, SLO thresholds
  - Source fetch errors: check network, adapter retries, LAW_CACHE_DIR
  - JWKS errors: verify key backend envs, Vault token/URL
## DEV Stack (docker-compose)

- Start stack:
  - `make run-stack`
- Smoke test (simple E2E):
  - `make smoke`
- Stop stack:
  - `make down-stack`

Grafana login (DEV): user `admin`, password `admin` (anonymous access also enabled).

