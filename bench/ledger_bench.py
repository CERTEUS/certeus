#!/usr/bin/env python3
"""
Simple, reproducible PostgreSQL insert benchmark for CERTEUS ledger-like workload.

Usage:
  python workspaces/certeus/bench/ledger_bench.py \
    --dsn postgresql://control:control_dev_pass@localhost:5432/control_test \
    --events 20000 --batch 1000 --concurrency 4 --out bench_result.json

Outputs JSON with throughput and timing metrics. Designed for local validation
and CI smoke (not a full TPC benchmark).
"""

from __future__ import annotations

import argparse
import asyncio as _asyncio
from dataclasses import asdict, dataclass
import json
import os
import time
from typing import Any

try:
    import asyncpg  # type: ignore
except Exception as e:  # pragma: no cover - optional at import time
    raise SystemExit("asyncpg is required. Install with: pip install asyncpg") from e


def _now_ns() -> int:
    return time.perf_counter_ns()


@dataclass
class BenchConfig:
    dsn: str
    events: int = 20000
    batch: int = 1000
    concurrency: int = 4
    out: str | None = None


@dataclass
class BenchResult:
    rid: str
    events: int
    batch: int
    concurrency: int
    duration_s: float
    throughput_eps: float
    started_ns: int
    finished_ns: int
    dsn_masked: str
    db_name: str | None
    notes: str = "Local reproducible harness"


def _mask_dsn(dsn: str) -> str:
    # mask password if present
    try:
        if "@" in dsn and "://" in dsn and ":" in dsn.split("@", 1)[0]:
            scheme, rest = dsn.split("://", 1)
            userpass, host = rest.split("@", 1)
            user = userpass.split(":", 1)[0]
            return f"{scheme}://{user}:***@{host}"
    except Exception:
        pass
    return dsn


async def _ensure_table(conn: asyncpg.Connection) -> None:  # type: ignore
    await conn.execute(
        """
        CREATE TABLE IF NOT EXISTS bench_events (
            id BIGSERIAL PRIMARY KEY,
            payload JSONB NOT NULL,
            ts TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        """
    )


async def _worker(pool: asyncpg.Pool, batches: list[list[dict[str, Any]]]) -> int:  # type: ignore
    inserted = 0
    async with pool.acquire() as conn:
        await _ensure_table(conn)
        stmt = await conn.prepare("INSERT INTO bench_events (payload) VALUES ($1)")
        for batch in batches:
            # Use executemany for batch insert
            await stmt.executemany([(json.dumps(x),) for x in batch])
            inserted += len(batch)
    return inserted


async def run_bench(cfg: BenchConfig) -> BenchResult:
    dsn = cfg.dsn
    events = max(1, int(cfg.events))
    batch = max(1, int(cfg.batch))
    conc = max(1, int(cfg.concurrency))

    # Partition work into batches of JSON payloads
    payloads = [
        {
            "case_id": i,
            "type": "bench_event",
            "amount": i % 1000,
            "meta": {"source": "ledger_bench", "i": i},
        }
        for i in range(events)
    ]
    batches: list[list[dict[str, Any]]] = [payloads[i : i + batch] for i in range(0, events, batch)]

    # Split batches across workers
    parts: list[list[list[dict[str, Any]]]] = [[] for _ in range(conc)]
    for idx, b in enumerate(batches):
        parts[idx % conc].append(b)

    started_ns = _now_ns()
    pool = await asyncpg.create_pool(dsn=dsn, min_size=min(1, conc), max_size=conc)
    try:
        inserted_counts = await _asyncio.gather(*[_worker(pool, part) for part in parts])
    finally:
        await pool.close()
    finished_ns = _now_ns()
    duration_s = (finished_ns - started_ns) / 1e9
    inserted = sum(inserted_counts)
    throughput = inserted / duration_s if duration_s > 0 else float("inf")

    # Attempt to get DB name
    db_name: str | None = None
    try:
        db_name = dsn.rsplit("/", 1)[-1]
    except Exception:
        pass

    rid = time.strftime("R:%Y-%m-%d:bench-local")
    res = BenchResult(
        rid=rid,
        events=inserted,
        batch=batch,
        concurrency=conc,
        duration_s=duration_s,
        throughput_eps=throughput,
        started_ns=started_ns,
        finished_ns=finished_ns,
        dsn_masked=_mask_dsn(dsn),
        db_name=db_name,
    )
    return res


def _parse_args() -> BenchConfig:
    parser = argparse.ArgumentParser(description="CERTEUS ledger bench harness")
    parser.add_argument(
        "--dsn",
        default=os.getenv("DATABASE_URL") or "postgresql://control:control_dev_pass@localhost:5432/control_test",
    )
    parser.add_argument("--events", type=int, default=20000)
    parser.add_argument("--batch", type=int, default=1000)
    parser.add_argument("--concurrency", type=int, default=4)
    parser.add_argument("--out", default=None)
    ns = parser.parse_args()
    return BenchConfig(dsn=ns.dsn, events=ns.events, batch=ns.batch, concurrency=ns.concurrency, out=ns.out)


def main() -> None:
    cfg = _parse_args()
    res = _asyncio.run(run_bench(cfg))
    data = asdict(res)
    print(json.dumps(data, indent=2))
    if cfg.out:
        with open(cfg.out, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)


if __name__ == "__main__":
    main()
