# CERTEUS — Handoff dla następnego agenta

## Status gałęzi i PR

- main: zielony; `Smoke (ubuntu/windows)` + `ci-gates` jako required checks.
- work/daily: zielony (agregat ci-gates + UI Smoke).
- Historia zresetowana (2025‑09‑02) do single‑root; archiwa starej historii: `origin/archive/old-main-*`, `origin/archive/old-daily-*`.

## Co dostarczono w tej iteracji (W9–W11)

- W9 (Security hardening)
  - OPA/Rego: `policies/security/roles.rego` + bramka `scripts/gates/roles_policy_gate.py` + Governance Pack `policies/governance/governance_pack.v0.1.yaml`.
  - Enforcement w ProofGate: per domena (lex/fin/sec), za flagą `FINE_GRAINED_ROLES`.
  - Bunkier/TEE: bramka `scripts/gates/security_bunker_gate.py` + stub `security/bunker/attestation.json` + runbook `docs/runbooks/security_bunker.md`.
  - PQ‑crypto: gate `scripts/gates/pqcrypto_gate.py` (require/ready) — informacyjny lub obowiązkowy przez env.
  - DP budgets: gate `scripts/gates/dp_budget_gate.py` (stub, STRICT_DP_BUDGET).

- W10 (Observability & SRE)
  - OTel opt‑in (kod): `monitoring/otel_setup.py`; włączone w `services/api_gateway/main.py` i `services/proofgate/app.py`.
  - OTel w CI: mock OTLP `scripts/otel/mock_otlp.py`, uruchamiany w workflowach; `OTEL_ENABLED=1`.
  - HTTP p95 histogram + middleware; `/metrics` z `Cache-Control: no-store`.
  - SRE Dashboard: `observability/grafana/certeus-sre-dashboard.json` (p95 by path/method/status, error‑rate; panele/staty).
  - DR Drill (Boundary) w Proof Gate CI: `scripts/dr/drill_boundary_failure.py`.

- W11 (Performance)
  - OpenAPI cache (Gateway/ProofGate) — mniejsze czasy `/openapi.json`.
  - Perf bench (in‑proc): `scripts/perf/quick_bench.py` → `out/perf_bench.json` (artefakt); PR komentarz z trendem (Δ vs poprzedni bieg).
  - Smoki: `/metrics`, `/openapi.json`, ProofGate `/healthz`.

## CI/PR — co jest zautomatyzowane

- PR summary (ci-gates) — komentarz zawiera:
  - Perf p95 i trend Δ (porównanie z `ci-status:ci/perf_bench.json`).
  - SLO p95/error_rate z tickiem (✅/❌) wg progów.
  - Smokes: metrics/openapi/governance ✅/❌.
  - Gates (lokalne kroki): style/lint/tests/perf/slo ✅/❌.
  - Workflows: Proof Gate / Gauge‑Gate / Path‑Coverage‑Gate / Boundary‑Rebuild‑Gate / asset‑guard (ticki przez API GitHub).
- Proof Gate workflow: ticki per krok (Gauge/Path/FIN/Bunker/Roles/Gov/Boundary/SLO) — dopisywane jako pliki `out/pg_*_ok.txt` i komentowane w PR (tylko PR/main; push: main).
- Supply‑chain: Trivy zapisuje SARIF, nie blokuje PR (exit-code=0).
- Auto‑merge: w repo włączony `allow_auto_merge=true`; branch protection ustawione na approvals=0 — PR zmerguje się po zielonych checkach.

## Użyte flagi i defaults w CI

- `.github/certeus.env.defaults` + `scripts/ci/load_env_defaults.py` (ładowanie do `$GITHUB_ENV`):
  - BUNKER=0, PROOFGATE_BUNKER=0, FINE_GRAINED_ROLES=1, PQCRYPTO_READY=1, PQCRYPTO_REQUIRE=0, STRICT_DP_BUDGET=0.
- W krokach „Tests” wymuszone `FINE_GRAINED_ROLES=0` (legacy testy ProofGate), test enforcementu ról steruje flagą lokalnie.
- OTel w CI: `OTEL_ENABLED=1`, `OTEL_EXPORTER_OTLP_ENDPOINT=http://127.0.0.1:4318` (mock OTLP).

## Pliki kluczowe (punkty wejścia)

- Workflows: `.github/workflows/ci-gates.yml`, `.github/workflows/proof-gate.yml`.
- Smoki: `scripts/smokes/metrics_smoke.py`, `scripts/smokes/openapi_smoke.py`, `scripts/smokes/proofgate_health_smoke.py`, `scripts/smokes/proofgate_roles_smoke.py`.
- Perf/SLO: `scripts/perf/quick_bench.py`, `scripts/slo_gate/measure_api.py`, `scripts/slo_gate/check_slo.py`.
- Governance: `policies/governance/governance_pack.v0.1.yaml`, `scripts/validate_governance_consistency.py`.
- Bunkier/PQ/DP: `scripts/gates/security_bunker_gate.py`, `scripts/gates/pqcrypto_gate.py`, `scripts/gates/dp_budget_gate.py`.
- ProofGate runtime: `services/proofgate/app.py` (enforcement ról per domena; cache OpenAPI).
- API Gateway: `services/api_gateway/main.py` (middleware p95; cache OpenAPI).
- Dashboardy i alerty: `observability/grafana/certeus-sre-dashboard.json`, `observability/prometheus/alert_rules_w10.yml`.

## Następne kroki (po merge do main)

- Trend perf — agregacja z ostatnich N biegów (ci-status) i rozszerzony komentarz PR.
- Ewentualne wzmocnienie gate’ów (Proof Gate) o twarde warunki dla PQ/DP w zależności od zmiennych repo.
- Dalsze optymalizacje p95 i paneli SRE.

## Status W14 (UX/A11y/i18n/Marketplace) — A8

- A11y/i18n: baseline smoke włączone w `ci-gates` (report-only) i testy zielone.
- Marketplace Policy Gate: uruchamiany raz w `ci-gates` (report-only), tick `out/marketplace_ok.txt` publikowany.
- Plugin Supply-Chain Gate: dodany (report-only) — weryfikuje SBOM/provenance dla `plugins/*` i publikuje tick `out/plugin_supply_ok.txt`.
- Porządek CI: usunięto duplikację kroku Marketplace Gate w `.github/workflows/ci-gates.yml` (jedna ścieżka egzekucji pozostaje).

### Następne kroki A8 (ciągłość W14)

- Supply-chain dla wtyczek: doprecyzowanie checklist (SBOM/provenance) — report-only w `ci-gates`.
- Observability: sanity dla trendów endpoint/tenant SLO (report-only), bez zmian progów.
- Dokumentacja: krótkie runbooki dla maintainerów (enforce flags, lokalne uruchomienia bramek).

## Uwagi operacyjne

- Jeśli czerwony check dotyczy braków importu w skryptach uruchamianych „jako plik” — wzorzec rozwiązania: dołączyć repo‑root do `sys.path` i dodać `# noqa: E402` przy importach aplikacji.
- Legacy testy ProofGate oczekują statusów PUBLISH/CONDITIONAL dla scenariuszy bez enforcementu — dlatego `FINE_GRAINED_ROLES=0` w „Tests”.
