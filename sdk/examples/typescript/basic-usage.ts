// CERTEUS TypeScript SDK - Basic Usage Example
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
