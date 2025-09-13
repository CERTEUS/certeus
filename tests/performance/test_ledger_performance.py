#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/performance/test_ledger_performance.py         |
# | ROLE: A2 - Ledger Performance Tests (≥1k events/s DoD)    |
# | PLIK: tests/performance/test_ledger_performance.py         |
# | ROLA: A2 - Ledger Performance Tests (≥1k events/s DoD)    |
# +-------------------------------------------------------------+

"""
PL: Testy wydajności Ledger - DoD: ≥1k events/s
EN: Ledger Performance Tests - DoD: ≥1k events/s

Test scenarios:
- Single event ingestion rate
- Batch event ingestion
- Concurrent client load
- Chain integrity verification performance
- S3 storage throughput
- Database connection pooling efficiency
"""

import asyncio
from datetime import datetime
import json
import random
import statistics
import time
from typing import Any

import asyncpg
import pytest

from services.ledger_service.postgres_ledger import LedgerConfig, PostgreSQLLedger


async def _check_postgres_available():
    """Check if PostgreSQL is available for testing"""
    try:
        conn = await asyncpg.connect('postgresql://certeus_test:password@localhost/certeus_test', timeout=2)
        await conn.close()
        return True
    except Exception:
        return False


# Skip entire performance test class if PostgreSQL not available
POSTGRES_AVAILABLE = asyncio.run(_check_postgres_available())


# === TEST CONFIGURATION ===


@pytest.fixture
def performance_ledger_config():
    """Performance test configuration"""
    return LedgerConfig(
        db_url="postgresql://certeus_test:password@localhost/certeus_test",
        db_pool_min=10,
        db_pool_max=50,  # Higher pool for performance tests
        db_timeout=60.0,
        s3_bucket="certeus-performance-test",
        s3_region="us-east-1",
        s3_endpoint_url="http://localhost:9000",  # MinIO
        batch_size=200,  # Larger batches for performance
        merkle_anchor_interval=5000,
        tsa_enabled=False,  # Disable for pure performance testing
    )


@pytest.fixture
async def performance_ledger(performance_ledger_config):
    """Performance ledger instance"""
    ledger = PostgreSQLLedger(performance_ledger_config)
    await ledger.initialize()

    yield ledger

    await ledger.close()


# === PERFORMANCE TESTS ===


@pytest.mark.skipif(not POSTGRES_AVAILABLE, reason="PostgreSQL not available (requires docker-compose up postgresql)")
class TestLedgerPerformance:
    """Performance test suite for A2 Ledger"""

    @pytest.mark.asyncio
    async def test_single_event_ingestion_rate(self, performance_ledger):
        """
        Test: Single-threaded event ingestion rate
        DoD Target: ≥1000 events/s sustained
        """

        # Warmup
        await self._warmup_ledger(performance_ledger)

        # Performance test parameters
        target_events = 5000
        test_duration_limit = 10.0  # seconds

        # Create test case
        case_id = f"PERF-{random.randint(100000, 999999)}"
        await performance_ledger.create_case(
            case_id, {"country": "PL", "domain": "performance_test"}, {"test_type": "single_ingestion"}
        )

        # Record events with timing
        start_time = time.time()
        events_recorded = 0
        latencies = []

        for i in range(target_events):
            event_start = time.time()

            await performance_ledger.record_event(
                event_type="PERFORMANCE_TEST",
                case_id=case_id,
                payload={
                    "sequence": i,
                    "timestamp": datetime.utcnow().isoformat(),
                    "data": f"performance_test_data_{i}",
                },
                actor="performance_test",
            )

            event_end = time.time()
            latencies.append((event_end - event_start) * 1000)  # ms
            events_recorded += 1

            # Check time limit
            elapsed = time.time() - start_time
            if elapsed >= test_duration_limit:
                break

        end_time = time.time()
        total_duration = end_time - start_time

        # Calculate metrics
        events_per_second = events_recorded / total_duration
        avg_latency = statistics.mean(latencies)
        p95_latency = statistics.quantiles(latencies, n=20)[18]  # 95th percentile
        p99_latency = statistics.quantiles(latencies, n=100)[98]  # 99th percentile

        # Performance report
        print("\n=== SINGLE EVENT INGESTION PERFORMANCE ===")
        print(f"Events recorded: {events_recorded}")
        print(f"Duration: {total_duration:.2f}s")
        print(f"Events/second: {events_per_second:.1f}")
        print(f"Average latency: {avg_latency:.2f}ms")
        print(f"P95 latency: {p95_latency:.2f}ms")
        print(f"P99 latency: {p99_latency:.2f}ms")

        # DoD Assertion: ≥1000 events/s
        assert events_per_second >= 1000, f"Performance below target: {events_per_second:.1f} events/s < 1000 events/s"

        # Additional quality assertions
        assert avg_latency <= 10.0, f"Average latency too high: {avg_latency:.2f}ms"
        assert p95_latency <= 50.0, f"P95 latency too high: {p95_latency:.2f}ms"

    @pytest.mark.asyncio
    async def test_batch_event_ingestion_rate(self, performance_ledger):
        """
        Test: Batch event ingestion performance
        DoD Target: ≥2000 events/s with batching
        """

        # Warmup
        await self._warmup_ledger(performance_ledger)

        # Test parameters
        batch_size = 100
        num_batches = 50
        total_events = batch_size * num_batches

        # Create test cases
        case_ids = [f"BATCH-{random.randint(100000, 999999)}" for _ in range(10)]
        for case_id in case_ids:
            await performance_ledger.create_case(
                case_id, {"country": "PL", "domain": "batch_test"}, {"test_type": "batch_ingestion"}
            )

        # Batch ingestion with timing
        start_time = time.time()
        batch_times = []

        for batch_num in range(num_batches):
            batch_start = time.time()

            # Create batch of events
            batch_tasks = []
            for i in range(batch_size):
                case_id = random.choice(case_ids)

                task = performance_ledger.record_event(
                    event_type="BATCH_TEST",
                    case_id=case_id,
                    payload={"batch": batch_num, "sequence": i, "data": f"batch_data_{batch_num}_{i}"},
                    actor="batch_test",
                )
                batch_tasks.append(task)

            # Execute batch concurrently
            await asyncio.gather(*batch_tasks)

            batch_end = time.time()
            batch_times.append(batch_end - batch_start)

        end_time = time.time()
        total_duration = end_time - start_time

        # Calculate metrics
        events_per_second = total_events / total_duration
        avg_batch_time = statistics.mean(batch_times)
        events_per_batch_second = batch_size / avg_batch_time

        # Performance report
        print("\n=== BATCH EVENT INGESTION PERFORMANCE ===")
        print(f"Total events: {total_events}")
        print(f"Batch size: {batch_size}")
        print(f"Number of batches: {num_batches}")
        print(f"Total duration: {total_duration:.2f}s")
        print(f"Overall events/second: {events_per_second:.1f}")
        print(f"Average batch time: {avg_batch_time:.3f}s")
        print(f"Events/second per batch: {events_per_batch_second:.1f}")

        # DoD Assertion: ≥2000 events/s with batching
        assert events_per_second >= 2000, (
            f"Batch performance below target: {events_per_second:.1f} events/s < 2000 events/s"
        )

    @pytest.mark.asyncio
    async def test_concurrent_client_load(self, performance_ledger):
        """
        Test: Multiple concurrent clients
        DoD Target: Maintain ≥1000 events/s with 10 concurrent clients
        """

        # Warmup
        await self._warmup_ledger(performance_ledger)

        # Test parameters
        num_clients = 10
        events_per_client = 200
        total_events = num_clients * events_per_client

        async def client_workload(client_id: int) -> dict[str, Any]:
            """Simulate single client workload"""

            case_id = f"CLIENT-{client_id:02d}-{random.randint(100000, 999999)}"
            await performance_ledger.create_case(
                case_id,
                {"country": "PL", "domain": "concurrent_test"},
                {"test_type": "concurrent_client", "client_id": client_id},
            )

            client_start = time.time()
            client_latencies = []

            for i in range(events_per_client):
                event_start = time.time()

                await performance_ledger.record_event(
                    event_type="CONCURRENT_TEST",
                    case_id=case_id,
                    payload={"client_id": client_id, "sequence": i, "data": f"client_{client_id}_data_{i}"},
                    actor=f"client_{client_id}",
                )

                event_end = time.time()
                client_latencies.append((event_end - event_start) * 1000)

            client_end = time.time()

            return {
                "client_id": client_id,
                "duration": client_end - client_start,
                "events": events_per_client,
                "latencies": client_latencies,
            }

        # Execute concurrent clients
        start_time = time.time()

        client_tasks = [client_workload(i) for i in range(num_clients)]
        client_results = await asyncio.gather(*client_tasks)

        end_time = time.time()
        total_duration = end_time - start_time

        # Analyze results
        all_latencies = []
        client_rates = []

        for result in client_results:
            client_rate = result["events"] / result["duration"]
            client_rates.append(client_rate)
            all_latencies.extend(result["latencies"])

        overall_rate = total_events / total_duration
        avg_client_rate = statistics.mean(client_rates)
        avg_latency = statistics.mean(all_latencies)
        p95_latency = statistics.quantiles(all_latencies, n=20)[18]

        # Performance report
        print("\n=== CONCURRENT CLIENT LOAD PERFORMANCE ===")
        print(f"Concurrent clients: {num_clients}")
        print(f"Events per client: {events_per_client}")
        print(f"Total events: {total_events}")
        print(f"Total duration: {total_duration:.2f}s")
        print(f"Overall events/second: {overall_rate:.1f}")
        print(f"Average client rate: {avg_client_rate:.1f} events/s")
        print(f"Average latency: {avg_latency:.2f}ms")
        print(f"P95 latency: {p95_latency:.2f}ms")

        # DoD Assertion: Maintain ≥1000 events/s under concurrent load
        assert overall_rate >= 1000, f"Concurrent performance below target: {overall_rate:.1f} events/s < 1000 events/s"

        # Quality assertions
        assert avg_latency <= 20.0, f"Average latency under load too high: {avg_latency:.2f}ms"
        assert all(rate >= 50 for rate in client_rates), "Some clients performed poorly"

    @pytest.mark.asyncio
    async def test_chain_integrity_verification_performance(self, performance_ledger):
        """
        Test: Chain integrity verification performance
        DoD Target: Verify 10k events in <5 seconds
        """

        # Setup test data
        case_id = f"CHAIN-{random.randint(100000, 999999)}"
        await performance_ledger.create_case(case_id, {"country": "PL", "domain": "chain_verification_test"})

        # Create chain of events
        num_events = 10000
        print(f"Creating {num_events} events for chain verification test...")

        setup_start = time.time()

        # Batch create events for setup
        batch_size = 500
        for batch_start in range(0, num_events, batch_size):
            batch_end = min(batch_start + batch_size, num_events)
            batch_tasks = []

            for i in range(batch_start, batch_end):
                task = performance_ledger.record_event(
                    event_type="CHAIN_VERIFICATION_TEST",
                    case_id=case_id,
                    payload={"sequence": i, "data": f"chain_data_{i}"},
                    actor="chain_test",
                )
                batch_tasks.append(task)

            await asyncio.gather(*batch_tasks)

            if batch_end % 2000 == 0:
                print(f"Created {batch_end} events...")

        setup_end = time.time()
        print(f"Setup completed in {setup_end - setup_start:.2f}s")

        # Verify chain integrity
        verification_start = time.time()

        integrity_result = await performance_ledger.verify_chain_integrity()

        verification_end = time.time()
        verification_duration = verification_end - verification_start

        # Calculate performance metrics
        events_verified_per_second = integrity_result.total_events / verification_duration

        # Performance report
        print("\n=== CHAIN INTEGRITY VERIFICATION PERFORMANCE ===")
        print(f"Events verified: {integrity_result.total_events}")
        print(f"Verification duration: {verification_duration:.2f}s")
        print(f"Events verified/second: {events_verified_per_second:.1f}")
        print(f"Chain valid: {integrity_result.is_valid}")
        print(f"Chain breaks: {len(integrity_result.chain_breaks)}")

        # DoD Assertion: Verify 10k events in <5 seconds (2k events/s verification rate)
        assert verification_duration <= 5.0, f"Verification too slow: {verification_duration:.2f}s > 5.0s"
        assert events_verified_per_second >= 2000, (
            f"Verification rate too low: {events_verified_per_second:.1f} events/s"
        )

        # Quality assertions
        assert integrity_result.is_valid, "Chain integrity verification failed"
        assert len(integrity_result.chain_breaks) == 0, f"Chain breaks detected: {integrity_result.chain_breaks}"

    @pytest.mark.asyncio
    async def test_s3_storage_performance(self, performance_ledger):
        """
        Test: S3 storage performance
        DoD Target: Store 100 bundles in <30 seconds
        """

        # Test parameters
        num_bundles = 100
        bundle_size = 1024 * 10  # 10KB per bundle

        # Generate test bundles
        test_bundles = []
        for i in range(num_bundles):
            bundle_data = {
                "bundle_id": f"perf_bundle_{i:04d}",
                "case_id": f"STOR-{random.randint(100000, 999999)}",
                "data": "x" * bundle_size,
                "metadata": {"performance_test": True, "sequence": i},
            }
            test_bundles.append(json.dumps(bundle_data).encode())

        # Storage performance test
        start_time = time.time()
        storage_times = []

        for i, bundle_data in enumerate(test_bundles):
            store_start = time.time()

            await performance_ledger.store_bundle(
                bundle_id=f"perf_bundle_{i:04d}",
                case_id=f"STOR-{random.randint(100000, 999999)}",
                bundle_data=bundle_data,
                bundle_hash=f"hash_{i:04d}" + "0" * 56,  # Mock hash
                signature_ed25519="mock_signature",
                public_key_id="mock_key_id",
            )

            store_end = time.time()
            storage_times.append(store_end - store_start)

        end_time = time.time()
        total_duration = end_time - start_time

        # Calculate metrics
        bundles_per_second = num_bundles / total_duration
        avg_storage_time = statistics.mean(storage_times)
        total_data_mb = (num_bundles * bundle_size) / (1024 * 1024)
        throughput_mbps = total_data_mb / total_duration

        # Performance report
        print("\n=== S3 STORAGE PERFORMANCE ===")
        print(f"Bundles stored: {num_bundles}")
        print(f"Bundle size: {bundle_size / 1024:.1f}KB")
        print(f"Total data: {total_data_mb:.1f}MB")
        print(f"Duration: {total_duration:.2f}s")
        print(f"Bundles/second: {bundles_per_second:.1f}")
        print(f"Throughput: {throughput_mbps:.2f} MB/s")
        print(f"Average storage time: {avg_storage_time:.3f}s")

        # DoD Assertion: 100 bundles in <30 seconds
        assert total_duration <= 30.0, f"Storage too slow: {total_duration:.2f}s > 30.0s"
        assert bundles_per_second >= 3.0, f"Storage rate too low: {bundles_per_second:.1f} bundles/s"

    async def _warmup_ledger(self, ledger: PostgreSQLLedger) -> None:
        """Warmup ledger with some baseline operations"""

        warmup_case = f"WARMUP-{random.randint(100000, 999999)}"
        await ledger.create_case(warmup_case, {"country": "PL", "domain": "warmup"})

        # Insert a few warmup events
        for i in range(10):
            await ledger.record_event(event_type="WARMUP", case_id=warmup_case, payload={"sequence": i})


# === PERFORMANCE BENCHMARK RUNNER ===


class PerformanceBenchmark:
    """Standalone performance benchmark runner"""

    def __init__(self, config: LedgerConfig):
        self.config = config
        self.ledger = None

    async def run_all_benchmarks(self) -> dict[str, Any]:
        """Run all performance benchmarks"""

        self.ledger = PostgreSQLLedger(self.config)
        await self.ledger.initialize()

        try:
            results = {}

            print("=== CERTEUS LEDGER PERFORMANCE BENCHMARK ===\n")

            # Single event ingestion
            results["single_event"] = await self._benchmark_single_events()

            # Batch ingestion
            results["batch_events"] = await self._benchmark_batch_events()

            # Concurrent load
            results["concurrent_load"] = await self._benchmark_concurrent_load()

            # Chain verification
            results["chain_verification"] = await self._benchmark_chain_verification()

            # Generate summary report
            self._print_summary_report(results)

            return results

        finally:
            await self.ledger.close()

    async def _benchmark_single_events(self) -> dict[str, Any]:
        """Benchmark single event ingestion"""

        print("1. Single Event Ingestion Benchmark")
        print("   Target: ≥1000 events/s")

        case_id = f"BENCH-{random.randint(100000, 999999)}"
        await self.ledger.create_case(case_id, {"country": "PL", "domain": "benchmark"})

        num_events = 2000
        start_time = time.time()

        for i in range(num_events):
            await self.ledger.record_event(event_type="BENCHMARK", case_id=case_id, payload={"sequence": i})

        end_time = time.time()
        duration = end_time - start_time
        rate = num_events / duration

        print(f"   Result: {rate:.1f} events/s ({'✓' if rate >= 1000 else '✗'})")
        print()

        return {"events": num_events, "duration": duration, "rate": rate, "target_met": rate >= 1000}

    async def _benchmark_batch_events(self) -> dict[str, Any]:
        """Benchmark batch event ingestion"""

        print("2. Batch Event Ingestion Benchmark")
        print("   Target: ≥2000 events/s")

        case_id = f"BATCH-{random.randint(100000, 999999)}"
        await self.ledger.create_case(case_id, {"country": "PL", "domain": "batch_benchmark"})

        batch_size = 100
        num_batches = 30
        total_events = batch_size * num_batches

        start_time = time.time()

        for batch_num in range(num_batches):
            tasks = []
            for i in range(batch_size):
                task = self.ledger.record_event(
                    event_type="BATCH_BENCHMARK", case_id=case_id, payload={"batch": batch_num, "sequence": i}
                )
                tasks.append(task)

            await asyncio.gather(*tasks)

        end_time = time.time()
        duration = end_time - start_time
        rate = total_events / duration

        print(f"   Result: {rate:.1f} events/s ({'✓' if rate >= 2000 else '✗'})")
        print()

        return {"events": total_events, "duration": duration, "rate": rate, "target_met": rate >= 2000}

    async def _benchmark_concurrent_load(self) -> dict[str, Any]:
        """Benchmark concurrent client load"""

        print("3. Concurrent Client Load Benchmark")
        print("   Target: ≥1000 events/s with 10 clients")

        num_clients = 10
        events_per_client = 150
        total_events = num_clients * events_per_client

        async def client_load(client_id: int):
            case_id = f"CONC-{client_id}-{random.randint(100000, 999999)}"
            await self.ledger.create_case(case_id, {"country": "PL", "domain": "concurrent"})

            for i in range(events_per_client):
                await self.ledger.record_event(
                    event_type="CONCURRENT_BENCHMARK", case_id=case_id, payload={"client": client_id, "sequence": i}
                )

        start_time = time.time()

        tasks = [client_load(i) for i in range(num_clients)]
        await asyncio.gather(*tasks)

        end_time = time.time()
        duration = end_time - start_time
        rate = total_events / duration

        print(f"   Result: {rate:.1f} events/s ({'✓' if rate >= 1000 else '✗'})")
        print()

        return {"events": total_events, "duration": duration, "rate": rate, "target_met": rate >= 1000}

    async def _benchmark_chain_verification(self) -> dict[str, Any]:
        """Benchmark chain integrity verification"""

        print("4. Chain Integrity Verification Benchmark")
        print("   Target: Verify 5000 events in <3 seconds")

        case_id = f"VERIFY-{random.randint(100000, 999999)}"
        await self.ledger.create_case(case_id, {"country": "PL", "domain": "verification"})

        # Create events to verify
        num_events = 5000
        batch_size = 200

        for batch_start in range(0, num_events, batch_size):
            batch_end = min(batch_start + batch_size, num_events)
            tasks = []

            for i in range(batch_start, batch_end):
                task = self.ledger.record_event(
                    event_type="VERIFICATION_BENCHMARK", case_id=case_id, payload={"sequence": i}
                )
                tasks.append(task)

            await asyncio.gather(*tasks)

        # Verify chain
        start_time = time.time()
        result = await self.ledger.verify_chain_integrity()
        end_time = time.time()

        duration = end_time - start_time
        rate = result.total_events / duration

        print(f"   Result: {duration:.2f}s for {result.total_events} events ({'✓' if duration <= 3.0 else '✗'})")
        print(f"   Rate: {rate:.1f} events verified/s")
        print()

        return {
            "events_verified": result.total_events,
            "duration": duration,
            "rate": rate,
            "target_met": duration <= 3.0,
            "chain_valid": result.is_valid,
        }

    def _print_summary_report(self, results: dict[str, Any]) -> None:
        """Print comprehensive summary report"""

        print("=== PERFORMANCE BENCHMARK SUMMARY ===")
        print()

        # Overall status
        all_targets_met = all(result.get("target_met", False) for result in results.values())

        print(f"Overall Status: {'✓ ALL TARGETS MET' if all_targets_met else '✗ SOME TARGETS MISSED'}")
        print()

        # Individual results
        for test_name, result in results.items():
            status = "✓ PASS" if result.get("target_met", False) else "✗ FAIL"
            print(f"{test_name.replace('_', ' ').title()}: {status}")

            if "rate" in result:
                print(f"  Rate: {result['rate']:.1f} events/s")
            if "duration" in result:
                print(f"  Duration: {result['duration']:.2f}s")

            print()


# === CLI RUNNER ===


async def main():
    """Run performance benchmarks from CLI"""

    print("CERTEUS Ledger Performance Benchmark")
    print("DoD Requirements: ≥1k events/s, chain integrity, <5s verification")
    print()

    # Use performance configuration
    config = LedgerConfig.from_env()
    config.db_pool_max = 50  # Optimize for performance testing

    benchmark = PerformanceBenchmark(config)
    results = await benchmark.run_all_benchmarks()

    # Exit with appropriate code
    all_passed = all(result.get("target_met", False) for result in results.values())
    exit(0 if all_passed else 1)


if __name__ == "__main__":
    asyncio.run(main())
