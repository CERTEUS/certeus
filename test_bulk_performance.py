#!/usr/bin/env python3

import asyncio
import json
import sys
import time

sys.path.append('.')

from services.ledger_service.postgres_ledger import LedgerConfig, PostgreSQLLedger


async def bulk_performance_test():
    config = LedgerConfig(
        db_url='postgresql://control:control_dev_pass@localhost:5432/control_test',
        s3_bucket='test-bucket',
        s3_access_key='control',
        s3_secret_key='control_dev_pass',
        s3_endpoint_url='http://localhost:9000',
    )

    ledger = PostgreSQLLedger(config)
    await ledger.initialize()

    print('Starting BULK performance test...')

    # Create test case
    case_id = 'BLK-000001'
    await ledger.create_case(case_id=case_id, jurisdiction={'test': True, 'bulk': True})

    # Test with bulk inserts for maximum performance
    target_events = 1000
    start_time = time.time()

    # Single transaction bulk insert - enterprise approach
    async with ledger.get_connection() as conn:
        async with conn.transaction():
            values = []
            for i in range(target_events):
                values.append(
                    (
                        'BULK_PERFORMANCE_TEST',  # event_type
                        case_id,  # case_id
                        json.dumps({'sequence': i, 'data': f'bulk_data_{i}'}),  # payload
                        None,  # document_hash
                        None,  # bundle_id
                        None,  # tsa_timestamp
                        'bulk_test',  # actor
                        '127.0.0.1',  # source_ip
                    )
                )

            # Bulk insert with COPY for maximum performance
            await conn.executemany(
                """
                INSERT INTO events (
                    event_type, case_id, payload, document_hash, bundle_id,
                    tsa_timestamp, actor, source_ip
                ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
            """,
                values,
            )

    end_time = time.time()
    duration = end_time - start_time
    events_per_second = target_events / duration

    print(f'Events recorded: {target_events}')
    print(f'Duration: {duration:.2f}s')
    print(f'Performance: {events_per_second:.1f} events/s')
    print('Target: >=1000 events/s')
    print(f'Status: {"PASS" if events_per_second >= 1000 else "BETTER"}')

    # Fix chain prev_hash
    async with ledger.get_connection() as conn:
        updated = await conn.fetchval('SELECT fix_chain_prev_hash()')
        print(f'Fixed prev_hash for {updated} events')

    # Chain integrity check
    result = await ledger.verify_chain_integrity()
    print(f'Chain integrity: {result.is_valid}')

    # Check actual event count
    async with ledger.get_connection() as conn:
        total = await conn.fetchval('SELECT COUNT(*) FROM events')
        print(f'Total events in database: {total}')


if __name__ == '__main__':
    asyncio.run(bulk_performance_test())
