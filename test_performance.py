#!/usr/bin/env python3

import asyncio
import sys
import time

sys.path.append('.')

from services.ledger_service.postgres_ledger import LedgerConfig, PostgreSQLLedger


async def performance_test():
    config = LedgerConfig(
        db_url='postgresql://control:control_dev_pass@localhost:5432/control_test',
        s3_bucket='test-bucket',
        s3_access_key='control',
        s3_secret_key='control_dev_pass',
        s3_endpoint_url='http://localhost:9000',
    )

    ledger = PostgreSQLLedger(config)
    await ledger.initialize()

    print('Starting performance test...')

    # Create test case
    case_id = 'PER-000001'
    await ledger.create_case(case_id=case_id, jurisdiction={'test': True, 'performance': True})

    # Test with 500 events (smaller batch for quick test)
    target_events = 500
    start_time = time.time()

    # Batch processing
    batch_size = 50
    for batch_start in range(0, target_events, batch_size):
        batch_tasks = []

        for i in range(batch_start, min(batch_start + batch_size, target_events)):
            task = ledger.record_event(
                case_id=case_id, event_type='PERFORMANCE_TEST', payload={'sequence': i, 'data': f'test_data_{i}'}
            )
            batch_tasks.append(task)

        await asyncio.gather(*batch_tasks)

    end_time = time.time()
    duration = end_time - start_time
    events_per_second = target_events / duration

    print(f'Events recorded: {target_events}')
    print(f'Duration: {duration:.2f}s')
    print(f'Performance: {events_per_second:.1f} events/s')
    print('Target: >=1000 events/s')
    print(f'Status: {"PASS" if events_per_second >= 1000 else "FAIL"}')

    # Fix chain prev_hash asynchronously
    async with ledger.get_connection() as conn:
        updated = await conn.fetchval('SELECT fix_chain_prev_hash()')
        print(f'Fixed prev_hash for {updated} events')

    # Final chain integrity check
    result = await ledger.verify_chain_integrity()
    print(f'Chain integrity after fix: {result.is_valid}')


if __name__ == '__main__':
    asyncio.run(performance_test())
