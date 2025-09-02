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

## Reading the SLO Dashboard

- Abstain Rate: current fraction of ABSTAIN decisions (`certeus_abstain_rate`). Sustained increase suggests policy/verifier or data issues.
- Compile/Verification p95 (ms): 95th percentile for proof compile/verification durations — budget and latency SLO proxy.
- Proof Verification Failures (rate): near‑real‑time failure rate; any value > 0 should page according to Alert rules.
- Source Fetch Errors (rate): link rot/cache issues; watch for spikes.
- HTTP p95 latency (ms) by path/method: service latency per route; track regressions.
- HTTP p95 latency (ms) by status: isolates high latency per status class (useful for 4xx/5xx hotspots).
- HTTP RPS by path/method/status: throughput and error mix across routes.
- HTTP 5xx rate (req/s): global failure rate; must be ≈ 0.

