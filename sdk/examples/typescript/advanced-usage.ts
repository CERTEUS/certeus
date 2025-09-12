// CERTEUS TypeScript SDK - Advanced Usage Example
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
