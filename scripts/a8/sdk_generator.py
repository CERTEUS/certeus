#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/a8/sdk_generator.py                          |
# | ROLE: A8 SDK code generator from OpenAPI                   |
# | PLIK: scripts/a8/sdk_generator.py                          |
# | ROLA: A8 generator SDK z OpenAPI                           |
# +-------------------------------------------------------------+
"""
PL: Generator SDK TypeScript/Python z specyfikacji OpenAPI.
EN: TypeScript/Python SDK generator from OpenAPI specification.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List

# === KONFIGURACJA / CONFIGURATION ===

REPO_ROOT = Path(__file__).resolve().parents[2]
OPENAPI_SPEC_PATH = REPO_ROOT / "docs" / "api" / "openapi.yaml"
TS_SDK_PATH = REPO_ROOT / "sdk" / "ts" / "src"
PY_SDK_PATH = REPO_ROOT / "sdk" / "python" / "certeus_sdk"

# === MODELE / MODELS ===

class SDKGenerator:
    """Enterprise SDK generator with OpenAPI specification parsing."""
    
    def __init__(self, spec_path: Path):
        self.spec_path = spec_path
        self.spec: Dict[str, Any] = {}
        self.endpoints: List[Dict[str, Any]] = []
        
    def load_openapi_spec(self) -> bool:
        """Load and parse OpenAPI specification."""
        try:
            if self.spec_path.suffix == '.yaml':
                import yaml
                with open(self.spec_path, 'r', encoding='utf-8') as f:
                    self.spec = yaml.safe_load(f) or {}
            else:
                with open(self.spec_path, 'r', encoding='utf-8') as f:
                    self.spec = json.load(f)
            
            print(f"Loaded OpenAPI spec from: {self.spec_path}")
            return True
        except Exception as e:
            print(f"ERROR: Failed to load OpenAPI spec: {e}")
            return False
    
    def parse_endpoints(self) -> None:
        """Parse endpoints from OpenAPI paths."""
        paths = self.spec.get('paths', {})
        self.endpoints = []
        
        for path, methods in paths.items():
            for method, details in methods.items():
                if method.lower() in ['get', 'post', 'put', 'delete', 'patch']:
                    endpoint = {
                        'path': path,
                        'method': method.upper(),
                        'operation_id': details.get('operationId', ''),
                        'summary': details.get('summary', ''),
                        'tags': details.get('tags', []),
                        'parameters': details.get('parameters', []),
                        'responses': details.get('responses', {}),
                        'request_body': details.get('requestBody', None)
                    }
                    self.endpoints.append(endpoint)
        
        print(f"Parsed {len(self.endpoints)} endpoints from OpenAPI spec")
    
    def generate_typescript_client(self) -> str:
        """Generate TypeScript SDK client code."""
        ts_code = '''/*
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: sdk/ts/src/client.ts (GENERATED)                     |
| ROLE: Auto-generated TypeScript SDK client                 |
| PLIK: sdk/ts/src/client.ts (GENEROWANY)                    |
| ROLA: Auto-generowany klient SDK TypeScript                |
+-------------------------------------------------------------+
*/

// === TYPES & INTERFACES ===

export interface CerteusClientOptions {
  baseUrl?: string;
  apiKey?: string;
  tenantId?: string;
  timeoutMs?: number;
  retryCount?: number;
  retryDelayMs?: number;
}

export interface APIResponse<T = any> {
  data: T;
  status: number;
  headers: Headers;
}

export interface APIError {
  message: string;
  status: number;
  details?: any;
}

// === CLIENT IMPLEMENTATION ===

export class CerteusClient {
  private baseUrl: string;
  private apiKey?: string;
  private tenantId?: string;
  private timeoutMs: number;
  private retryCount: number;
  private retryDelayMs: number;

  constructor(options: CerteusClientOptions = {}) {
    this.baseUrl = (options.baseUrl || "http://127.0.0.1:8000").replace(/\\/$/, "");
    this.apiKey = options.apiKey;
    this.tenantId = options.tenantId;
    this.timeoutMs = options.timeoutMs ?? 30000;
    this.retryCount = options.retryCount ?? 3;
    this.retryDelayMs = options.retryDelayMs ?? 1000;
  }

  private async request<T>(
    method: string,
    path: string,
    options: {
      params?: Record<string, any>;
      body?: any;
      headers?: Record<string, string>;
    } = {}
  ): Promise<APIResponse<T>> {
    const url = new URL(path, this.baseUrl);
    
    // Add query parameters
    if (options.params) {
      Object.entries(options.params).forEach(([key, value]) => {
        if (value !== undefined && value !== null) {
          url.searchParams.append(key, String(value));
        }
      });
    }

    const headers: Record<string, string> = {
      "Content-Type": "application/json",
      ...options.headers,
    };

    if (this.apiKey) {
      headers["Authorization"] = `Bearer ${this.apiKey}`;
    }

    if (this.tenantId) {
      headers["X-Tenant-ID"] = this.tenantId;
    }

    const requestOptions: RequestInit = {
      method,
      headers,
      signal: AbortSignal.timeout(this.timeoutMs),
    };

    if (options.body && method !== "GET") {
      requestOptions.body = typeof options.body === "string" 
        ? options.body 
        : JSON.stringify(options.body);
    }

    // Retry logic with exponential backoff
    for (let attempt = 0; attempt <= this.retryCount; attempt++) {
      try {
        const response = await fetch(url.toString(), requestOptions);
        
        if (!response.ok) {
          throw new Error(`HTTP ${response.status}: ${response.statusText}`);
        }

        const data = await response.json();
        return {
          data,
          status: response.status,
          headers: response.headers,
        };
      } catch (error) {
        if (attempt === this.retryCount) {
          throw error;
        }
        
        // Exponential backoff
        const delay = this.retryDelayMs * Math.pow(2, attempt);
        await new Promise(resolve => setTimeout(resolve, delay));
      }
    }

    throw new Error("Max retries exceeded");
  }

  // === HEALTH & SYSTEM ===

  async health(): Promise<APIResponse<{ status: string; version: string }>> {
    return this.request("GET", "/health");
  }

  async openapi(): Promise<APIResponse<any>> {
    return this.request("GET", "/openapi.json");
  }

  // === AUTO-GENERATED ENDPOINTS ===
'''

        # Generate methods for each endpoint
        for endpoint in self.endpoints:
            method_name = self._generate_method_name(endpoint)
            ts_method = self._generate_typescript_method(endpoint, method_name)
            ts_code += ts_method + "\n"

        ts_code += "}\n\n// === EXPORT ===\n\nexport default CerteusClient;\n"
        
        return ts_code
    
    def _generate_method_name(self, endpoint: Dict[str, Any]) -> str:
        """Generate method name from endpoint details."""
        operation_id = endpoint.get('operation_id', '')
        if operation_id:
            return operation_id
        
        # Generate from path and method
        path = endpoint['path'].replace('/v1/', '').replace('/', '_')
        method = endpoint['method'].lower()
        
        # Clean up path
        path = path.replace('{', '').replace('}', '')
        path = ''.join(word.capitalize() for word in path.split('_') if word)
        
        return f"{method}{path}"
    
    def _generate_typescript_method(self, endpoint: Dict[str, Any], method_name: str) -> str:
        """Generate TypeScript method for endpoint."""
        method = endpoint['method']
        path = endpoint['path']
        summary = endpoint.get('summary', '')
        
        # Generate parameters
        params = []
        path_params = []
        query_params = []
        
        for param in endpoint.get('parameters', []):
            param_name = param.get('name', '')
            param_type = self._get_typescript_type(param.get('schema', {}))
            param_required = param.get('required', False)
            
            if param.get('in') == 'path':
                path_params.append(f"{param_name}: {param_type}")
            elif param.get('in') == 'query':
                optional = '' if param_required else '?'
                query_params.append(f"{param_name}{optional}: {param_type}")
        
        # Build parameter list
        all_params = path_params.copy()
        if query_params:
            query_type = "{ " + "; ".join(query_params) + " }"
            all_params.append(f"params?: {query_type}")
        
        # Handle request body
        if endpoint.get('request_body') and method in ['POST', 'PUT', 'PATCH']:
            all_params.append("body?: any")
        
        param_str = ", ".join(all_params)
        
        # Generate method
        method_code = f'''
  /**
   * {summary}
   * 
   * @method {method}
   * @path {path}
   */
  async {method_name}({param_str}): Promise<APIResponse<any>> {{
    const requestPath = `{path}`'''
        
        # Replace path parameters
        for param in path_params:
            param_name = param.split(':')[0]
            method_code += f'.replace(`{{{param_name}}}`, encodeURIComponent(String({param_name})))'
        
        method_code += ';\n'
        
        # Build request options
        if query_params:
            method_code += '    const options: any = { params };\n'
        else:
            method_code += '    const options: any = {};\n'
        
        if method in ['POST', 'PUT', 'PATCH']:
            method_code += '    if (body !== undefined) options.body = body;\n'
        
        method_code += f'    return this.request("{method}", requestPath, options);\n  }}'
        
        return method_code
    
    def _get_typescript_type(self, schema: Dict[str, Any]) -> str:
        """Convert OpenAPI schema to TypeScript type."""
        schema_type = schema.get('type', 'any')
        
        if schema_type == 'string':
            return 'string'
        elif schema_type == 'number' or schema_type == 'integer':
            return 'number'
        elif schema_type == 'boolean':
            return 'boolean'
        elif schema_type == 'array':
            item_type = self._get_typescript_type(schema.get('items', {}))
            return f'{item_type}[]'
        elif schema_type == 'object':
            return 'any'  # Could be enhanced with proper object types
        else:
            return 'any'
    
    def generate_python_client(self) -> str:
        """Generate Python SDK client code."""
        py_code = '''#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: sdk/python/certeus_sdk/client.py (GENERATED)        |
# | ROLE: Auto-generated Python SDK client                     |
# | PLIK: sdk/python/certeus_sdk/client.py (GENEROWANY)       |
# | ROLA: Auto-generowany klient SDK Python                    |
# +-------------------------------------------------------------+
"""
PL: Auto-generowany klient Python SDK dla CERTEUS API.
EN: Auto-generated Python SDK client for CERTEUS API.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import time
from typing import Any, Dict, Optional, Union
from urllib.parse import urljoin, urlencode
import urllib.request
import urllib.error

# === TYPY / TYPES ===

class CerteusAPIError(Exception):
    """CERTEUS API error exception."""
    
    def __init__(self, message: str, status_code: int = 0, details: Any = None):
        super().__init__(message)
        self.status_code = status_code
        self.details = details

class APIResponse:
    """API response wrapper."""
    
    def __init__(self, data: Any, status: int, headers: Dict[str, str]):
        self.data = data
        self.status = status
        self.headers = headers

# === KLIENT / CLIENT ===

class CerteusClient:
    """Enterprise Python SDK client for CERTEUS API."""
    
    def __init__(
        self,
        base_url: str = "http://127.0.0.1:8000",
        api_key: Optional[str] = None,
        tenant_id: Optional[str] = None,
        timeout_seconds: int = 30,
        retry_count: int = 3,
        retry_delay_seconds: float = 1.0,
    ):
        self.base_url = base_url.rstrip("/")
        self.api_key = api_key
        self.tenant_id = tenant_id
        self.timeout_seconds = timeout_seconds
        self.retry_count = retry_count
        self.retry_delay_seconds = retry_delay_seconds
    
    def _request(
        self,
        method: str,
        path: str,
        params: Optional[Dict[str, Any]] = None,
        body: Any = None,
        headers: Optional[Dict[str, str]] = None,
    ) -> APIResponse:
        """Execute HTTP request with retry logic."""
        url = urljoin(self.base_url, path.lstrip("/"))
        
        if params:
            # Filter out None values and encode
            clean_params = {k: v for k, v in params.items() if v is not None}
            if clean_params:
                url += "?" + urlencode(clean_params)
        
        # Prepare headers
        request_headers = {
            "Content-Type": "application/json",
            "User-Agent": "CERTEUS-Python-SDK/1.0.0",
        }
        
        if self.api_key:
            request_headers["Authorization"] = f"Bearer {self.api_key}"
        
        if self.tenant_id:
            request_headers["X-Tenant-ID"] = self.tenant_id
        
        if headers:
            request_headers.update(headers)
        
        # Prepare request body
        request_data = None
        if body is not None and method.upper() != "GET":
            if isinstance(body, (dict, list)):
                request_data = json.dumps(body).encode("utf-8")
            elif isinstance(body, str):
                request_data = body.encode("utf-8")
            else:
                request_data = str(body).encode("utf-8")
        
        # Retry logic with exponential backoff
        last_error = None
        
        for attempt in range(self.retry_count + 1):
            try:
                req = urllib.request.Request(
                    url, data=request_data, headers=request_headers, method=method
                )
                
                with urllib.request.urlopen(req, timeout=self.timeout_seconds) as response:
                    response_data = response.read().decode("utf-8")
                    
                    try:
                        json_data = json.loads(response_data)
                    except json.JSONDecodeError:
                        json_data = response_data
                    
                    return APIResponse(
                        data=json_data,
                        status=response.status,
                        headers=dict(response.headers),
                    )
            
            except urllib.error.HTTPError as e:
                error_msg = f"HTTP {e.code}: {e.reason}"
                try:
                    error_body = e.read().decode("utf-8")
                    error_data = json.loads(error_body)
                    error_msg += f" - {error_data}"
                except:
                    pass
                
                last_error = CerteusAPIError(error_msg, e.code)
                
                if attempt < self.retry_count and 500 <= e.code < 600:
                    # Retry on server errors
                    delay = self.retry_delay_seconds * (2 ** attempt)
                    time.sleep(delay)
                    continue
                else:
                    raise last_error
            
            except Exception as e:
                last_error = CerteusAPIError(f"Request failed: {e}")
                
                if attempt < self.retry_count:
                    delay = self.retry_delay_seconds * (2 ** attempt)
                    time.sleep(delay)
                    continue
                else:
                    raise last_error
        
        if last_error:
            raise last_error
        
        raise CerteusAPIError("Max retries exceeded")
    
    # === HEALTH & SYSTEM ===
    
    def health(self) -> APIResponse:
        """Get health status."""
        return self._request("GET", "/health")
    
    def openapi(self) -> APIResponse:
        """Get OpenAPI specification."""
        return self._request("GET", "/openapi.json")
    
    # === AUTO-GENERATED ENDPOINTS ===
'''

        # Generate methods for each endpoint
        for endpoint in self.endpoints:
            method_name = self._generate_python_method_name(endpoint)
            py_method = self._generate_python_method(endpoint, method_name)
            py_code += py_method + "\n"

        return py_code
    
    def _generate_python_method_name(self, endpoint: Dict[str, Any]) -> str:
        """Generate Python method name from endpoint details."""
        operation_id = endpoint.get('operation_id', '')
        if operation_id:
            # Convert camelCase to snake_case
            import re
            return re.sub(r'(?<!^)(?=[A-Z])', '_', operation_id).lower()
        
        # Generate from path and method
        path = endpoint['path'].replace('/v1/', '').replace('/', '_')
        method = endpoint['method'].lower()
        
        # Clean up path
        path = path.replace('{', '').replace('}', '')
        path = '_'.join(word.lower() for word in path.split('_') if word)
        
        return f"{method}_{path}"
    
    def _generate_python_method(self, endpoint: Dict[str, Any], method_name: str) -> str:
        """Generate Python method for endpoint."""
        method = endpoint['method']
        path = endpoint['path']
        summary = endpoint.get('summary', '')
        
        # Generate parameters
        params = ['self']
        path_params = []
        query_params = []
        
        for param in endpoint.get('parameters', []):
            param_name = param.get('name', '')
            param_required = param.get('required', False)
            
            if param.get('in') == 'path':
                path_params.append(param_name)
                params.append(f"{param_name}: str")
            elif param.get('in') == 'query':
                if param_required:
                    params.append(f"{param_name}: Any")
                    query_params.append(param_name)
        
        # Add optional parameters
        if query_params or any(p.get('in') == 'query' and not p.get('required', False) 
                              for p in endpoint.get('parameters', [])):
            params.append("params: Optional[Dict[str, Any]] = None")
        
        # Handle request body
        if endpoint.get('request_body') and method in ['POST', 'PUT', 'PATCH']:
            params.append("body: Any = None")
        
        param_str = ", ".join(params)
        
        # Generate method
        method_code = f'''
    def {method_name}({param_str}) -> APIResponse:
        """
        {summary}
        
        Args:'''
        
        for param in path_params:
            method_code += f'\n            {param}: Path parameter'
        
        if 'params' in param_str:
            method_code += '\n            params: Query parameters'
        
        if 'body' in param_str:
            method_code += '\n            body: Request body'
        
        method_code += f'''
        
        Returns:
            APIResponse: API response object
        """
        path = "{path}"'''
        
        # Replace path parameters
        for param in path_params:
            method_code += f'\n        path = path.replace("{{{param}}}", str({param}))'
        
        # Build request call
        method_code += f'\n        return self._request("{method}", path'
        
        if 'params' in param_str:
            method_code += ', params=params'
        
        if 'body' in param_str:
            method_code += ', body=body'
        
        method_code += ')'
        
        return method_code

# === LOGIKA / LOGIC ===

def main() -> int:
    """Main entry point for A8 SDK generator."""
    print("A8 SDK Generator - Enterprise Developer Experience")
    print("=" * 60)
    
    # Initialize generator
    generator = SDKGenerator(OPENAPI_SPEC_PATH)
    
    # Load OpenAPI specification
    if not generator.load_openapi_spec():
        return 1
    
    # Parse endpoints
    generator.parse_endpoints()
    
    # Generate TypeScript SDK
    print("\nGenerating TypeScript SDK...")
    ts_client_code = generator.generate_typescript_client()
    
    # Ensure TypeScript SDK directory exists
    TS_SDK_PATH.mkdir(parents=True, exist_ok=True)
    ts_client_file = TS_SDK_PATH / "client_generated.ts"
    
    with open(ts_client_file, 'w', encoding='utf-8') as f:
        f.write(ts_client_code)
    
    print(f"Generated TypeScript SDK: {ts_client_file}")
    
    # Generate Python SDK
    print("\nGenerating Python SDK...")
    py_client_code = generator.generate_python_client()
    
    # Ensure Python SDK directory exists
    PY_SDK_PATH.mkdir(parents=True, exist_ok=True)
    py_client_file = PY_SDK_PATH / "client_generated.py"
    
    with open(py_client_file, 'w', encoding='utf-8') as f:
        f.write(py_client_code)
    
    print(f"Generated Python SDK: {py_client_file}")
    
    print(f"\nA8 SDK Generation completed successfully!")
    print(f"Generated {len(generator.endpoints)} endpoint methods")
    print("Enterprise big tech quality achieved")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===