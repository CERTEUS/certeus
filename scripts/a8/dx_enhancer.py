#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/a8/dx_enhancer.py                            |
# | ROLE: A8 Developer Experience enhancement tools            |
# | PLIK: scripts/a8/dx_enhancer.py                            |
# | ROLA: A8 narzędzia usprawniające doświadczenie developerów |
# +-------------------------------------------------------------+
"""
PL: Narzędzia usprawniające doświadczenie developerów (DX) dla CERTEUS SDK.
EN: Developer Experience (DX) enhancement tools for CERTEUS SDK.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path
import sys

# === KONFIGURACJA / CONFIGURATION ===

REPO_ROOT = Path(__file__).resolve().parents[2]
EXAMPLES_DIR = REPO_ROOT / "sdk" / "examples"
DOCS_DIR = REPO_ROOT / "docs" / "sdk"
PLAYGROUND_DIR = REPO_ROOT / "clients" / "web" / "playground"

# === MODELE / MODELS ===


class DXEnhancer:
    """Developer Experience enhancement suite."""

    def __init__(self):
        self.examples_dir = EXAMPLES_DIR
        self.docs_dir = DOCS_DIR
        self.playground_dir = PLAYGROUND_DIR

    def ensure_directories(self) -> None:
        """Ensure all required directories exist."""
        directories = [
            self.examples_dir,
            self.examples_dir / "typescript",
            self.examples_dir / "python",
            self.examples_dir / "quickstart",
            self.docs_dir,
            self.playground_dir,
        ]

        for directory in directories:
            directory.mkdir(parents=True, exist_ok=True)
            print(f"Ensured directory: {directory}")

    def generate_typescript_examples(self) -> None:
        """Generate comprehensive TypeScript SDK examples."""
        print("Generating TypeScript SDK examples...")

        # Basic usage example
        basic_example = '''// CERTEUS TypeScript SDK - Basic Usage Example
import { CerteusClient } from '@certeus/sdk';

async function basicUsage() {
  // Initialize client
  const client = new CerteusClient({
    baseUrl: 'https://api.certeus.dev',
    apiKey: 'your-api-key',
    tenantId: 'your-tenant-id'
  });

  try {
    // Health check
    const health = await client.health();
    console.log('API Status:', health.data.status);

    // Get OpenAPI specification
    const spec = await client.openapi();
    console.log('API Version:', spec.data.info.version);

  } catch (error) {
    console.error('API Error:', error.message);
  }
}

basicUsage();
'''

        # Advanced example with error handling
        advanced_example = '''// CERTEUS TypeScript SDK - Advanced Usage Example
import { CerteusClient, APIError } from '@certeus/sdk';

class CerteusService {
  private client: CerteusClient;

  constructor(config: {
    baseUrl: string;
    apiKey: string;
    tenantId?: string;
  }) {
    this.client = new CerteusClient({
      ...config,
      timeoutMs: 30000,
      retryCount: 3,
      retryDelayMs: 1000
    });
  }

  async healthCheck(): Promise<boolean> {
    try {
      const response = await this.client.health();
      return response.data.status === 'ok';
    } catch (error) {
      console.error('Health check failed:', error);
      return false;
    }
  }

  async withRetry<T>(operation: () => Promise<T>, maxRetries = 3): Promise<T> {
    for (let attempt = 1; attempt <= maxRetries; attempt++) {
      try {
        return await operation();
      } catch (error) {
        if (attempt === maxRetries) throw error;
        
        const delay = Math.pow(2, attempt) * 1000;
        console.log(`Attempt ${attempt} failed, retrying in ${delay}ms...`);
        await new Promise(resolve => setTimeout(resolve, delay));
      }
    }
    throw new Error('Max retries exceeded');
  }
}

// Usage
async function advancedExample() {
  const service = new CerteusService({
    baseUrl: process.env.CERTEUS_API_URL || 'http://localhost:8000',
    apiKey: process.env.CERTEUS_API_KEY!,
    tenantId: process.env.CERTEUS_TENANT_ID
  });

  // Health check with retry
  const isHealthy = await service.withRetry(() => service.healthCheck());
  console.log('Service healthy:', isHealthy);
}

advancedExample().catch(console.error);
'''

        # React hook example
        react_example = '''// CERTEUS TypeScript SDK - React Hook Example
import React, { createContext, useContext, useEffect, useState } from 'react';
import { CerteusClient, APIResponse } from '@certeus/sdk';

interface CerteusContextType {
  client: CerteusClient | null;
  isConnected: boolean;
  error: string | null;
}

const CerteusContext = createContext<CerteusContextType>({
  client: null,
  isConnected: false,
  error: null
});

export const CerteusProvider: React.FC<{
  children: React.ReactNode;
  config: {
    baseUrl: string;
    apiKey: string;
    tenantId?: string;
  };
}> = ({ children, config }) => {
  const [client] = useState(() => new CerteusClient(config));
  const [isConnected, setIsConnected] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const checkConnection = async () => {
      try {
        await client.health();
        setIsConnected(true);
        setError(null);
      } catch (err) {
        setIsConnected(false);
        setError(err instanceof Error ? err.message : 'Connection failed');
      }
    };

    checkConnection();
    const interval = setInterval(checkConnection, 30000); // Check every 30s

    return () => clearInterval(interval);
  }, [client]);

  return (
    <CerteusContext.Provider value={{ client, isConnected, error }}>
      {children}
    </CerteusContext.Provider>
  );
};

export const useCerteus = () => {
  const context = useContext(CerteusContext);
  if (!context) {
    throw new Error('useCerteus must be used within a CerteusProvider');
  }
  return context;
};

// Usage in component
export const ApiStatusComponent: React.FC = () => {
  const { client, isConnected, error } = useCerteus();
  const [apiInfo, setApiInfo] = useState<any>(null);

  useEffect(() => {
    if (!client || !isConnected) return;

    const fetchApiInfo = async () => {
      try {
        const response = await client.openapi();
        setApiInfo(response.data.info);
      } catch (err) {
        console.error('Failed to fetch API info:', err);
      }
    };

    fetchApiInfo();
  }, [client, isConnected]);

  if (error) {
    return <div className="error">Connection Error: {error}</div>;
  }

  if (!isConnected) {
    return <div className="loading">Connecting to CERTEUS API...</div>;
  }

  return (
    <div className="api-status">
      <h3>CERTEUS API Status</h3>
      <p>Status: Connected</p>
      {apiInfo && (
        <div>
          <p>Version: {apiInfo.version}</p>
          <p>Title: {apiInfo.title}</p>
        </div>
      )}
    </div>
  );
};
'''

        # Save examples
        examples = [
            ("basic-usage.ts", basic_example),
            ("advanced-usage.ts", advanced_example),
            ("react-hooks.tsx", react_example),
        ]

        ts_examples_dir = self.examples_dir / "typescript"
        for filename, content in examples:
            example_file = ts_examples_dir / filename
            with open(example_file, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"Generated TypeScript example: {example_file}")

    def generate_python_examples(self) -> None:
        """Generate comprehensive Python SDK examples."""
        print("Generating Python SDK examples...")

        # Basic usage example
        basic_example = '''#!/usr/bin/env python3
"""CERTEUS Python SDK - Basic Usage Example"""

from certeus_sdk import CerteusClient, CerteusAPIError

def basic_usage():
    """Basic SDK usage example."""
    # Initialize client
    client = CerteusClient(
        base_url='https://api.certeus.dev',
        api_key='your-api-key',
        tenant_id='your-tenant-id'
    )
    
    try:
        # Health check
        health_response = client.health()
        print(f"API Status: {health_response.data['status']}")
        
        # Get OpenAPI specification
        spec_response = client.openapi()
        print(f"API Version: {spec_response.data['info']['version']}")
        
    except CerteusAPIError as e:
        print(f"API Error: {e} (Status: {e.status_code})")
    except Exception as e:
        print(f"Unexpected error: {e}")

if __name__ == "__main__":
    basic_usage()
'''

        # Advanced example with async support
        advanced_example = '''#!/usr/bin/env python3
"""CERTEUS Python SDK - Advanced Usage Example"""

import asyncio
import logging
import os
from typing import Any, Dict, Optional

from certeus_sdk import CerteusClient, CerteusAPIError

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class CerteusService:
    """Advanced CERTEUS service wrapper with error handling and retries."""
    
    def __init__(self, config: Dict[str, Any]):
        self.client = CerteusClient(
            base_url=config.get('base_url', 'http://localhost:8000'),
            api_key=config.get('api_key'),
            tenant_id=config.get('tenant_id'),
            timeout_seconds=config.get('timeout', 30),
            retry_count=config.get('retry_count', 3),
            retry_delay_seconds=config.get('retry_delay', 1.0)
        )
        self.logger = logger
    
    def health_check(self) -> bool:
        """Check API health status."""
        try:
            response = self.client.health()
            is_healthy = response.data.get('status') == 'ok'
            self.logger.info(f"Health check: {'PASS' if is_healthy else 'FAIL'}")
            return is_healthy
        except CerteusAPIError as e:
            self.logger.error(f"Health check failed: {e}")
            return False
    
    def with_retry(self, operation, *args, **kwargs):
        """Execute operation with retry logic."""
        max_retries = 3
        last_error = None
        
        for attempt in range(max_retries + 1):
            try:
                return operation(*args, **kwargs)
            except Exception as e:
                last_error = e
                if attempt < max_retries:
                    delay = 2 ** attempt
                    self.logger.warning(f"Attempt {attempt + 1} failed, retrying in {delay}s: {e}")
                    time.sleep(delay)
                else:
                    self.logger.error(f"All retry attempts failed: {e}")
        
        raise last_error
    
    def get_api_info(self) -> Optional[Dict[str, Any]]:
        """Get API information with retry."""
        try:
            response = self.with_retry(self.client.openapi)
            return response.data.get('info', {})
        except Exception as e:
            self.logger.error(f"Failed to get API info: {e}")
            return None

def main():
    """Advanced usage example."""
    # Load configuration from environment
    config = {
        'base_url': os.getenv('CERTEUS_API_URL', 'http://localhost:8000'),
        'api_key': os.getenv('CERTEUS_API_KEY'),
        'tenant_id': os.getenv('CERTEUS_TENANT_ID'),
        'timeout': int(os.getenv('CERTEUS_TIMEOUT', '30')),
        'retry_count': int(os.getenv('CERTEUS_RETRY_COUNT', '3'))
    }
    
    # Initialize service
    service = CerteusService(config)
    
    # Health check with retry
    if service.health_check():
        logger.info("Service is healthy")
        
        # Get API information
        api_info = service.get_api_info()
        if api_info:
            logger.info(f"API Version: {api_info.get('version')}")
            logger.info(f"API Title: {api_info.get('title')}")
    else:
        logger.error("Service health check failed")

if __name__ == "__main__":
    main()
'''

        # Context manager example
        context_example = '''#!/usr/bin/env python3
"""CERTEUS Python SDK - Context Manager Example"""

import time
from contextlib import contextmanager
from typing import Generator

from certeus_sdk import CerteusClient, CerteusAPIError

@contextmanager
def certeus_client_context(
    base_url: str,
    api_key: str = None,
    tenant_id: str = None
) -> Generator[CerteusClient, None, None]:
    """Context manager for CERTEUS client with automatic cleanup."""
    client = CerteusClient(
        base_url=base_url,
        api_key=api_key,
        tenant_id=tenant_id
    )
    
    start_time = time.time()
    print(f"Initializing CERTEUS client for: {base_url}")
    
    try:
        # Verify connection
        health = client.health()
        if health.data.get('status') != 'ok':
            raise ConnectionError("API health check failed")
        
        yield client
        
    except CerteusAPIError as e:
        print(f"CERTEUS API Error: {e}")
        raise
    except Exception as e:
        print(f"Unexpected error: {e}")
        raise
    finally:
        duration = time.time() - start_time
        print(f"CERTEUS client session completed in {duration:.2f}s")

def example_with_context():
    """Example using context manager."""
    with certeus_client_context(
        base_url='http://localhost:8000',
        api_key='your-api-key',
        tenant_id='demo'
    ) as client:
        
        # Get API specification
        spec = client.openapi()
        paths = spec.data.get('paths', {})
        print(f"API has {len(paths)} endpoints")
        
        # List some paths
        for path in list(paths.keys())[:5]:
            print(f"  - {path}")

if __name__ == "__main__":
    example_with_context()
'''

        # Save examples
        examples = [
            ("basic_usage.py", basic_example),
            ("advanced_usage.py", advanced_example),
            ("context_manager.py", context_example),
        ]

        py_examples_dir = self.examples_dir / "python"
        for filename, content in examples:
            example_file = py_examples_dir / filename
            with open(example_file, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"Generated Python example: {example_file}")

    def generate_quickstart_guide(self) -> None:
        """Generate quickstart documentation."""
        print("Generating quickstart guides...")

        quickstart_content = '''# CERTEUS SDK Quick Start Guide

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
'''

        quickstart_file = self.examples_dir / "quickstart" / "README.md"
        with open(quickstart_file, 'w', encoding='utf-8') as f:
            f.write(quickstart_content)

        print(f"Generated quickstart guide: {quickstart_file}")

    def generate_documentation(self) -> None:
        """Generate comprehensive SDK documentation."""
        print("Generating SDK documentation...")

        # TypeScript SDK documentation
        ts_docs = '''# CERTEUS TypeScript SDK

Enterprise-grade TypeScript/JavaScript SDK for CERTEUS API.

## Features

- 🎯 **Type Safety**: Full TypeScript definitions
- 🔄 **Retry Logic**: Built-in exponential backoff
- 🔑 **Multiple Auth**: API keys, JWT, OAuth support
- 📱 **Universal**: Works in Node.js, Deno, and browsers
- 🚀 **Performance**: Optimized for enterprise use
- 📊 **Monitoring**: Built-in metrics and logging

## Installation

```bash
npm install @certeus/sdk
```

## Quick Start

```typescript
import { CerteusClient } from '@certeus/sdk';

const client = new CerteusClient({
  baseUrl: 'https://api.certeus.dev',
  apiKey: process.env.CERTEUS_API_KEY,
  tenantId: process.env.CERTEUS_TENANT_ID
});

// Health check
const health = await client.health();
console.log('API Status:', health.data.status);
```

## Configuration

### Client Options

```typescript
interface CerteusClientOptions {
  baseUrl?: string;        // API base URL
  apiKey?: string;         // Authentication key
  tenantId?: string;       // Tenant identifier
  timeoutMs?: number;      // Request timeout (default: 30000)
  retryCount?: number;     // Retry attempts (default: 3)
  retryDelayMs?: number;   // Initial retry delay (default: 1000)
}
```

### Environment Variables

```bash
CERTEUS_API_URL=https://api.certeus.dev
CERTEUS_API_KEY=your-api-key
CERTEUS_TENANT_ID=your-tenant-id
```

## Error Handling

```typescript
import { CerteusClient, APIError } from '@certeus/sdk';

try {
  const result = await client.someOperation();
} catch (error) {
  if (error instanceof APIError) {
    console.error('API Error:', error.message, 'Status:', error.status);
  } else {
    console.error('Unexpected error:', error);
  }
}
```

## Advanced Usage

### Custom Retry Logic

```typescript
const client = new CerteusClient({
  baseUrl: 'https://api.certeus.dev',
  retryCount: 5,
  retryDelayMs: 2000,
  timeoutMs: 60000
});
```

### React Integration

```typescript
import React, { useEffect, useState } from 'react';
import { CerteusClient } from '@certeus/sdk';

const useAPI = () => {
  const [client] = useState(() => new CerteusClient({
    baseUrl: process.env.REACT_APP_API_URL,
    apiKey: process.env.REACT_APP_API_KEY
  }));
  
  const [status, setStatus] = useState('connecting');
  
  useEffect(() => {
    client.health()
      .then(() => setStatus('connected'))
      .catch(() => setStatus('error'));
  }, [client]);
  
  return { client, status };
};
```

## API Reference

[Complete API documentation](./api-reference.md)

## Examples

- [Basic Usage](../examples/typescript/basic-usage.ts)
- [Advanced Usage](../examples/typescript/advanced-usage.ts)
- [React Hooks](../examples/typescript/react-hooks.tsx)

## Support

- [GitHub Issues](https://github.com/certeus/certeus/issues)
- [Discord Community](https://discord.gg/certeus)
- [Enterprise Support](mailto:enterprise@certeus.dev)
'''

        # Python SDK documentation
        py_docs = '''# CERTEUS Python SDK

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
'''

        # Save documentation
        ts_docs_file = self.docs_dir / "typescript.md"
        with open(ts_docs_file, 'w', encoding='utf-8') as f:
            f.write(ts_docs)
        print(f"Generated TypeScript docs: {ts_docs_file}")

        py_docs_file = self.docs_dir / "python.md"
        with open(py_docs_file, 'w', encoding='utf-8') as f:
            f.write(py_docs)
        print(f"Generated Python docs: {py_docs_file}")

    def generate_playground_config(self) -> None:
        """Generate interactive playground configuration."""
        print("Generating playground configuration...")

        playground_config = {
            "title": "CERTEUS API Playground",
            "description": "Interactive API explorer for CERTEUS",
            "version": "1.0.0",
            "endpoints": [
                {
                    "name": "Health Check",
                    "method": "GET",
                    "path": "/health",
                    "description": "Check API health status",
                    "example": {
                        "curl": "curl -X GET https://api.certeus.dev/health",
                        "javascript": "const response = await fetch('/health'); const data = await response.json();",
                        "python": "response = client.health(); print(response.data)",
                    },
                },
                {
                    "name": "OpenAPI Spec",
                    "method": "GET",
                    "path": "/openapi.json",
                    "description": "Get OpenAPI specification",
                    "example": {
                        "curl": "curl -X GET https://api.certeus.dev/openapi.json",
                        "javascript": "const spec = await client.openapi(); console.log(spec.data.info);",
                        "python": "spec = client.openapi(); print(spec.data['info'])",
                    },
                },
            ],
            "sdk_examples": {
                "typescript": {
                    "installation": "npm install @certeus/sdk",
                    "import": "import { CerteusClient } from '@certeus/sdk';",
                    "client_init": "const client = new CerteusClient({ baseUrl: 'https://api.certeus.dev' });",
                },
                "python": {
                    "installation": "pip install certeus-sdk",
                    "import": "from certeus_sdk import CerteusClient",
                    "client_init": "client = CerteusClient(base_url='https://api.certeus.dev')",
                },
            },
        }

        config_file = self.playground_dir / "config.json"
        with open(config_file, 'w', encoding='utf-8') as f:
            json.dump(playground_config, f, indent=2)

        print(f"Generated playground config: {config_file}")


# === LOGIKA / LOGIC ===


def main() -> int:
    """Main entry point for A8 DX enhancer."""
    print("A8 Developer Experience Enhancer")
    print("=" * 60)

    # Initialize DX enhancer
    enhancer = DXEnhancer()

    # Ensure all directories exist
    enhancer.ensure_directories()

    # Generate examples and documentation
    enhancer.generate_typescript_examples()
    enhancer.generate_python_examples()
    enhancer.generate_quickstart_guide()
    enhancer.generate_documentation()
    enhancer.generate_playground_config()

    print("\n" + "=" * 60)
    print("A8 Developer Experience Enhancement completed!")
    print("Generated:")
    print("  - TypeScript SDK examples")
    print("  - Python SDK examples")
    print("  - Quickstart documentation")
    print("  - Comprehensive SDK docs")
    print("  - Interactive playground config")
    print("\nEnterprise big tech developer experience achieved!")

    return 0


if __name__ == "__main__":
    sys.exit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
