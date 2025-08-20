# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: Makefile                                                      |
# | ROLE:                                                                |
# |  PL/EN: Skróty: lint, test, proof-gate, bench, packs.               |
# +=====================================================================+

.PHONY: lint test fmt proof-gate bench packs

lint:
\tuv run ruff check .

fmt:
\tuv run ruff format .

test:
\tuv run pytest -q

proof-gate:
\tuv run python scripts/verify_bundle.py

bench:
\tuv run python scripts/perf_bench.py

packs:
\tuv run python repo_to_packs.py . --out ingest_repo --pack-chars 250000 --file-chunk 80000 --overlap 2000
