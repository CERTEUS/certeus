#!/usr/bin/env python3

import asyncio
import sys

sys.path.append('.')

from services.ledger_service.postgres_ledger import LedgerConfig, PostgreSQLLedger


async def stress_test_concurrent():
    config = LedgerConfig(
        db_url='postgresql://control:control_dev_pass@localhost:5432/control_test',
        s3_bucket='test-bucket',
        s3_access_key='control',
        s3_secret_key='control_dev_pass',
        s3_endpoint_url='http://localhost:9000',
    )

    ledger = PostgreSQLLedger(config)
    await ledger.initialize()

    print('Starting concurrent stress test with new SEQUENCE-based trigger...')

    # Create 100 events concurrently (should be atomic with sequence)
    tasks = []
    for i in range(100):
        case_id = f'TST-{i:06d}'

        # Create case first
        await ledger.create_case(case_id=case_id, jurisdiction={'test': True, 'concurrent': i})

        # Create events concurrently
        for j in range(5):
            task = ledger.record_event(
                case_id=case_id, event_type='CONCURRENT_TEST', payload={'test': i, 'event': j, 'concurrent': True}
            )
            tasks.append(task)

    # Execute all 500 events concurrently
    await asyncio.gather(*tasks)

    print('Concurrent operations completed!')

    # Verify chain integrity
    result = await ledger.verify_chain_integrity()
    print(f'Chain integrity: {result}')

    # Check database state
    async with ledger.get_connection() as conn:
        total_events = await conn.fetchval('SELECT COUNT(*) FROM events')
        duplicates = await conn.fetchval('SELECT COUNT(*) FROM v_chain_integrity WHERE NOT chain_valid')
        chain_positions = await conn.fetch(
            'SELECT chain_position, COUNT(*) as cnt FROM events GROUP BY chain_position HAVING COUNT(*) > 1 ORDER BY chain_position LIMIT 5'
        )

        print(f'Total events in DB: {total_events}')
        print(f'Chain integrity problems: {duplicates}')
        print(f'Duplicate chain positions: {len(chain_positions)}')
        if chain_positions:
            print(f'First duplicates: {chain_positions}')


if __name__ == '__main__':
    asyncio.run(stress_test_concurrent())
