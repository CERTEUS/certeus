// CERTEUS TypeScript SDK - React Hook Example
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
