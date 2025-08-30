# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: Makefile                                                      |
# | ROLE:                                                                |
# |  PL/EN: Skróty: lint, test, proof-gate, bench, packs.               |
# +=====================================================================+

.PHONY: lint test fmt proof-gate bench packs run-api run-proofgate gates gates-gauge gates-coverage gates-boundary token cerctl

lint:
	uv run ruff check .

fmt:
	uv run ruff format .

test:
	uv run pytest -q

proof-gate:
	uv run python scripts/verify_bundle.py

bench:
	uv run python scripts/perf_bench.py

packs:
	uv run python repo_to_packs.py . --out ingest_repo --pack-chars 250000 --file-chunk 80000 --overlap 2000

# --- Runtime helpers ---
run-api:
	uv run uvicorn services.api_gateway.main:app --reload --port 8081

run-proofgate:
	uv run uvicorn services.proofgate.app:app --reload --port 8085

# --- CI Gates (local) ---
gates-gauge:
	uv run python scripts/gates/compute_gauge_drift.py --flags data/flags/kk.flags.json --out out/gauge.json
	uv run python scripts/gates/gauge_gate.py --epsilon 1e-3 --input out/gauge.json

gates-coverage:
	uv run python scripts/gates/compute_lexqft_coverage.py --flags data/flags/kk.flags.json --out out/lexqft_coverage.json
	uv run python scripts/gates/path_coverage_gate.py --min-gamma 0.90 --max-uncaptured 0.05 --input out/lexqft_coverage.json

gates-boundary:
	uv run python scripts/gates/compute_boundary_report.py
	STRICT_BOUNDARY_REBUILD=1 uv run python scripts/gates/boundary_rebuild_gate.py --report out/boundary_report.json

gates: gates-gauge gates-coverage gates-boundary

boundary-reconstruct:
	uv run python scripts/boundary_reconstruct.py

# --- PCO Token utility ---
token:
	@echo "Usage examples:" && \
	echo "  uv run python scripts/pco_token_tool.py gen-key" && \
	echo "  uv run python scripts/pco_token_tool.py export-jwks --pub <PUB_B64URL>" && \
	echo "  uv run python scripts/pco_token_tool.py sign --sec <SEC_B64URL> --payload '{\"sub\":\"tenant-1\"}'" && \
	echo "  uv run python scripts/pco_token_tool.py verify --pub <PUB_B64URL> --token <JWS>"

cerctl:
	uv run python scripts/cerctl.py $(ARGS)
