# CERTEUS Ledger Benchmark — REPORT TEMPLATE

This document captures hardware, database tuning, and command lines required to reproduce performance claims.

## Hardware & OS

- CPU: <model, cores/threads>
- RAM: <size>
- Disk: <NVMe/SATA, model>
- OS: <Linux distro/kernel or Windows/macOS>

## PostgreSQL

- Version: `psql --version`
- Config: see `bench/pg.conf.sample` (paste diffs if changed)

## Reproduce

```bash
export DATABASE_URL="postgresql://control:control_dev_pass@localhost:5432/control_test"
python workspaces/certeus/bench/ledger_bench.py --events 50000 --batch 2000 --concurrency 8 --out bench_result.json
```

## Result

Paste the JSON from `bench_result.json` and link the PCO RID published at `/pco/public/{rid}` when available.

```json
{
  "rid": "R:2025-09-12:bench-local",
  "events": 50000,
  "batch": 2000,
  "concurrency": 8,
  "duration_s": 0.0,
  "throughput_eps": 0.0,
  "started_ns": 0,
  "finished_ns": 0,
  "dsn_masked": "postgresql://control:***@localhost:5432/control_test",
  "db_name": "control_test",
  "notes": "Local reproducible harness"
}
```

## Evidence (PCO)

When publishing, attach the JSON to a PCO bundle and expose it via `/pco/public/{rid}`. Reference it in README under “Proof of Performance & Security”.

