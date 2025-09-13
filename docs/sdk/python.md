# CERTEUS Python SDK

Enterprise-grade Python SDK for CERTEUS API.

## Features

- 🐍 **Python 3.11+**: Modern Python support
- 🔄 **Async/Sync**: Both synchronous and asynchronous clients
- 🔑 **Multiple Auth**: API keys, JWT, OAuth support
- 🛡️ **Type Safety**: Full type hints and mypy compliance
- 🚀 **Performance**: Optimized for enterprise use
- 📊 **Monitoring**: Built-in metrics and logging

## Installation

```bash
pip install certeus-sdk
```

## Quick Start

```python
from certeus_sdk import CerteusClient

client = CerteusClient(
    base_url='https://api.certeus.dev',
    api_key='your-api-key',
    tenant_id='your-tenant-id'
)

# Health check
health = client.health()
print(f"API Status: {health.data['status']}")
```

## Configuration

### Client Options

```python
client = CerteusClient(
    base_url='https://api.certeus.dev',
    api_key='your-api-key',
    tenant_id='your-tenant-id',
    timeout_seconds=30,
    retry_count=3,
    retry_delay_seconds=1.0
)
```

### Environment Variables

```bash
export CERTEUS_API_URL="https://api.certeus.dev"
export CERTEUS_API_KEY="your-api-key"
export CERTEUS_TENANT_ID="your-tenant-id"
```

## Error Handling

```python
from certeus_sdk import CerteusClient, CerteusAPIError

try:
    result = client.some_operation()
    print(f"Success: {result.data}")
except CerteusAPIError as e:
    print(f"API Error: {e} (Status: {e.status_code})")
    if hasattr(e, 'details'):
        print(f"Details: {e.details}")
except Exception as e:
    print(f"Unexpected error: {e}")
```

## Advanced Usage

### Context Manager

```python
from contextlib import contextmanager

@contextmanager
def certeus_session(**config):
    client = CerteusClient(**config)
    try:
        # Verify connection
        client.health()
        yield client
    finally:
        # Cleanup if needed
        pass

# Usage
with certeus_session(base_url='https://api.certeus.dev') as client:
    result = client.some_operation()
```

### Async Support (Coming Soon)

```python
import asyncio
from certeus_sdk import AsyncCerteusClient

async def async_example():
    async with AsyncCerteusClient(base_url='https://api.certeus.dev') as client:
        health = await client.health()
        return health.data

result = asyncio.run(async_example())
```

### Custom Retry Logic

```python
import time
import random
from certeus_sdk import CerteusAPIError

def with_backoff(operation, max_retries=5):
    for attempt in range(max_retries):
        try:
            return operation()
        except CerteusAPIError as e:
            if e.status_code == 429:  # Rate limited
                delay = (2 ** attempt) + random.uniform(0, 1)
                time.sleep(delay)
            else:
                raise
    raise Exception("Max retries exceeded")

# Usage
result = with_backoff(lambda: client.some_operation())
```

## API Reference

[Complete API documentation](./api-reference.md)

## Examples

- [Basic Usage](../examples/python/basic_usage.py)
- [Advanced Usage](../examples/python/advanced_usage.py)
- [Context Manager](../examples/python/context_manager.py)

## Support

- [GitHub Issues](https://github.com/certeus/certeus/issues)
- [Discord Community](https://discord.gg/certeus)
- [Enterprise Support](mailto:enterprise@certeus.dev)
