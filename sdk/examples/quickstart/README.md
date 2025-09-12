# CERTEUS SDK Quick Start Guide

Get up and running with CERTEUS in under 5 minutes.

## Prerequisites

- **TypeScript/Node.js**: Node.js 18+ or Deno 1.30+
- **Python**: Python 3.11+ with pip
- **API Access**: CERTEUS API endpoint and credentials

## Installation

### TypeScript/JavaScript
```bash
npm install @certeus/sdk
# or
yarn add @certeus/sdk
```

### Python
```bash
pip install certeus-sdk
```

## Basic Usage

### TypeScript
```typescript
import { CerteusClient } from '@certeus/sdk';

const client = new CerteusClient({
  baseUrl: 'https://api.certeus.dev',
  apiKey: 'your-api-key',
  tenantId: 'your-tenant-id'
});

// Health check
const health = await client.health();
console.log('Status:', health.data.status);
```

### Python
```python
from certeus_sdk import CerteusClient

client = CerteusClient(
    base_url='https://api.certeus.dev',
    api_key='your-api-key',
    tenant_id='your-tenant-id'
)

# Health check
health = client.health()
print(f"Status: {health.data['status']}")
```

## Configuration Options

### Client Options
| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `baseUrl` | string | `http://127.0.0.1:8000` | API base URL |
| `apiKey` | string | - | Authentication API key |
| `tenantId` | string | - | Tenant identifier |
| `timeoutMs` | number | 30000 | Request timeout (TypeScript) |
| `timeout_seconds` | int | 30 | Request timeout (Python) |
| `retryCount` | number | 3 | Number of retry attempts |
| `retryDelayMs` | number | 1000 | Initial retry delay |

### Environment Variables
```bash
export CERTEUS_API_URL="https://api.certeus.dev"
export CERTEUS_API_KEY="your-api-key"
export CERTEUS_TENANT_ID="your-tenant-id"
```

## Error Handling

### TypeScript
```typescript
try {
  const result = await client.someOperation();
  console.log('Success:', result.data);
} catch (error) {
  if (error.status === 401) {
    console.error('Authentication failed');
  } else if (error.status >= 500) {
    console.error('Server error:', error.message);
  } else {
    console.error('Client error:', error.message);
  }
}
```

### Python
```python
from certeus_sdk import CerteusAPIError

try:
    result = client.some_operation()
    print(f"Success: {result.data}")
except CerteusAPIError as e:
    if e.status_code == 401:
        print("Authentication failed")
    elif e.status_code >= 500:
        print(f"Server error: {e}")
    else:
        print(f"Client error: {e}")
```

## Best Practices

### 1. Use Environment Variables
Store sensitive configuration in environment variables, not in code.

### 2. Implement Retry Logic
The SDK includes built-in retry logic, but you can customize it:

```typescript
const client = new CerteusClient({
  baseUrl: 'https://api.certeus.dev',
  retryCount: 5,
  retryDelayMs: 2000
});
```

### 3. Handle Rate Limits
Implement exponential backoff for rate-limited operations:

```python
import time
import random

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
```

### 4. Monitor API Health
Regularly check API health in production:

```typescript
// Health check every 30 seconds
setInterval(async () => {
  try {
    await client.health();
    console.log('API healthy');
  } catch (error) {
    console.error('API unhealthy:', error.message);
  }
}, 30000);
```

## Next Steps

- 📚 [Complete API Documentation](./api-reference.md)
- 🔧 [Advanced Examples](../examples/)
- 🚀 [Production Deployment Guide](./production.md)
- 🐛 [Troubleshooting Guide](./troubleshooting.md)

## Support

- 📖 [Documentation](https://docs.certeus.dev)
- 💬 [Community Discord](https://discord.gg/certeus)
- 🐞 [Issue Tracker](https://github.com/certeus/certeus/issues)
- 📧 [Enterprise Support](mailto:enterprise@certeus.dev)
