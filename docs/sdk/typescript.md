# CERTEUS TypeScript SDK

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
