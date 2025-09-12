/*
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
    this.baseUrl = (options.baseUrl || "http://127.0.0.1:8000").replace(/\/$/, "");
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

  /**
   * Create and publish ProofBundle (v0.2)
   * 
   * @method POST
   * @path /v1/pco/bundle
   */
  async postPcoBundle(body?: any): Promise<APIResponse<any>> {
    const requestPath = `/v1/pco/bundle`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Get public PCO payload
   * 
   * @method GET
   * @path /v1/pco/public/{case_id}
   */
  async getPcoPublicCaseId(case_id: string, params?: { include_evidence?: boolean }): Promise<APIResponse<any>> {
    const requestPath = `/v1/pco/public/{case_id}`.replace(`{case_id}`, encodeURIComponent(String(case_id)));
    const options: any = { params };
    return this.request("GET", requestPath, options);
  }

  /**
   * Verify PCO Bundle or public payload
   * 
   * @method POST
   * @path /v1/verify
   */
  async postVerify(body?: any): Promise<APIResponse<any>> {
    const requestPath = `/v1/verify`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * JWKS
   * 
   * @method GET
   * @path /.well-known/jwks.json
   */
  async get.well-knownJwks.json(): Promise<APIResponse<any>> {
    const requestPath = `/.well-known/jwks.json`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * [DEPRECATED] Get public PCO payload
   * 
   * @method GET
   * @path /pco/public/{case_id}
   */
  async getPcoPublicCaseId(case_id: string): Promise<APIResponse<any>> {
    const requestPath = `/pco/public/{case_id}`.replace(`{case_id}`, encodeURIComponent(String(case_id)));
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Compute legal geodesic (CFE)
   * 
   * @method POST
   * @path /v1/cfe/geodesic
   */
  async postCfeGeodesic(): Promise<APIResponse<any>> {
    const requestPath = `/v1/cfe/geodesic`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Compute legal horizon (CFE)
   * 
   * @method POST
   * @path /v1/cfe/horizon
   */
  async postCfeHorizon(): Promise<APIResponse<any>> {
    const requestPath = `/v1/cfe/horizon`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Lensing map (CFE)
   * 
   * @method GET
   * @path /v1/cfe/lensing
   */
  async getCfeLensing(): Promise<APIResponse<any>> {
    const requestPath = `/v1/cfe/lensing`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Warm up CFE cache for case list
   * 
   * @method POST
   * @path /v1/cfe/cache/warm
   */
  async postCfeCacheWarm(body?: any): Promise<APIResponse<any>> {
    const requestPath = `/v1/cfe/cache/warm`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Build lensing map from FIN signals
   * 
   * @method POST
   * @path /v1/cfe/lensing/from_fin
   */
  async postCfeLensingFromFin(body?: any): Promise<APIResponse<any>> {
    const requestPath = `/v1/cfe/lensing/from_fin`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Initialize QTMP case predistribution
   * 
   * @method POST
   * @path /v1/qtm/init_case
   */
  async postQtmInitCase(): Promise<APIResponse<any>> {
    const requestPath = `/v1/qtm/init_case`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Perform QTMP measurement
   * 
   * @method POST
   * @path /v1/qtm/measure
   */
  async postQtmMeasure(): Promise<APIResponse<any>> {
    const requestPath = `/v1/qtm/measure`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Compute commutator (QTMP)
   * 
   * @method POST
   * @path /v1/qtm/commutator
   */
  async postQtmCommutator(): Promise<APIResponse<any>> {
    const requestPath = `/v1/qtm/commutator`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Find variable entanglement
   * 
   * @method POST
   * @path /v1/qtm/find_entanglement
   */
  async postQtmFindEntanglement(): Promise<APIResponse<any>> {
    const requestPath = `/v1/qtm/find_entanglement`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Plan evidence horizon (HDE)
   * 
   * @method POST
   * @path /v1/devices/horizon_drive/plan
   */
  async postDevicesHorizonDrivePlan(): Promise<APIResponse<any>> {
    const requestPath = `/v1/devices/horizon_drive/plan`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Optimize expectation via qOracle
   * 
   * @method POST
   * @path /v1/devices/qoracle/expectation
   */
  async postDevicesQoracleExpectation(): Promise<APIResponse<any>> {
    const requestPath = `/v1/devices/qoracle/expectation`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Create entanglement certificate
   * 
   * @method POST
   * @path /v1/devices/entangle
   */
  async postDevicesEntangle(): Promise<APIResponse<any>> {
    const requestPath = `/v1/devices/entangle`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Reconcile chronosync coordinates
   * 
   * @method POST
   * @path /v1/devices/chronosync/reconcile
   */
  async postDevicesChronosyncReconcile(): Promise<APIResponse<any>> {
    const requestPath = `/v1/devices/chronosync/reconcile`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Register UPN
   * 
   * @method POST
   * @path /v1/upn/register
   */
  async postUpnRegister(): Promise<APIResponse<any>> {
    const requestPath = `/v1/upn/register`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Revoke UPN
   * 
   * @method POST
   * @path /v1/upn/revoke
   */
  async postUpnRevoke(): Promise<APIResponse<any>> {
    const requestPath = `/v1/upn/revoke`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Decision Replay
   * 
   * @method POST
   * @path /v1/dr/replay
   */
  async postDrReplay(): Promise<APIResponse<any>> {
    const requestPath = `/v1/dr/replay`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Decision Recall
   * 
   * @method POST
   * @path /v1/dr/recall
   */
  async postDrRecall(): Promise<APIResponse<any>> {
    const requestPath = `/v1/dr/recall`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Publication decision (ProofGate)
   * 
   * @method POST
   * @path /defx/reason
   */
  async postDefxReason(): Promise<APIResponse<any>> {
    const requestPath = `/defx/reason`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Public payload of ProofBundle (zero PII)
   * 
   * @method GET
   * @path /pco/public/{rid}
   */
  async getPcoPublicRid(rid: string): Promise<APIResponse<any>> {
    const requestPath = `/pco/public/{rid}`.replace(`{rid}`, encodeURIComponent(String(rid)));
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Prometheus metrics
   * 
   * @method GET
   * @path /metrics
   */
  async getMetrics(): Promise<APIResponse<any>> {
    const requestPath = `/metrics`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Cache a legal source by URI
   * 
   * @method POST
   * @path /v1/sources/cache
   */
  async postSourcesCache(body?: any): Promise<APIResponse<any>> {
    const requestPath = `/v1/sources/cache`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Publication decision (ProofGate)
   * 
   * @method POST
   * @path /v1/proofgate/publish
   */
  async postProofgatePublish(body?: any): Promise<APIResponse<any>> {
    const requestPath = `/v1/proofgate/publish`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * List packs
   * 
   * @method GET
   * @path /v1/packs
   */
  async getPacks(): Promise<APIResponse<any>> {
    const requestPath = `/v1/packs`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Handle pack action
   * 
   * @method POST
   * @path /v1/packs/handle
   */
  async postPacksHandle(): Promise<APIResponse<any>> {
    const requestPath = `/v1/packs/handle`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * List installed plugins
   * 
   * @method GET
   * @path /v1/marketplace/plugins
   */
  async getMarketplacePlugins(): Promise<APIResponse<any>> {
    const requestPath = `/v1/marketplace/plugins`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Verify signed manifest
   * 
   * @method POST
   * @path /v1/marketplace/verify_manifest
   */
  async postMarketplaceVerifyManifest(): Promise<APIResponse<any>> {
    const requestPath = `/v1/marketplace/verify_manifest`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Install/upgrade plugin (signed)
   * 
   * @method POST
   * @path /v1/marketplace/install
   */
  async postMarketplaceInstall(): Promise<APIResponse<any>> {
    const requestPath = `/v1/marketplace/install`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Validate plugin manifest without install
   * 
   * @method POST
   * @path /v1/marketplace/dry_run
   */
  async postMarketplaceDryRun(): Promise<APIResponse<any>> {
    const requestPath = `/v1/marketplace/dry_run`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Get tenant quota (cost tokens)
   * 
   * @method GET
   * @path /v1/billing/quota
   */
  async getBillingQuota(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/quota`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Set tenant quota (cost tokens)
   * 
   * @method POST
   * @path /v1/billing/quota
   */
  async postBillingQuota(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/quota`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Refund units to tenant budget
   * 
   * @method POST
   * @path /v1/billing/refund
   */
  async postBillingRefund(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/refund`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Allocate units to current tenant (PENDING → allocate)
   * 
   * @method POST
   * @path /v1/billing/allocate
   */
  async postBillingAllocate(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/allocate`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Get billing policies (tiers and tenants)
   * 
   * @method GET
   * @path /v1/billing/policies
   */
  async getBillingPolicies(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/policies`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Resolve tenant tier
   * 
   * @method GET
   * @path /v1/billing/tenant_tier
   */
  async getBillingTenantTier(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/tenant_tier`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Estimate cost units for action
   * 
   * @method POST
   * @path /v1/billing/estimate
   */
  async postBillingEstimate(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/estimate`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Recommend tier based on action and volume
   * 
   * @method GET
   * @path /v1/billing/recommendation
   */
  async getBillingRecommendation(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/recommendation`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Admin: set tenant tier (DEV)
   * 
   * @method POST
   * @path /v1/billing/admin/set_tier
   */
  async postBillingAdminSetTier(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/admin/set_tier`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Admin: reload policies from file (DEV)
   * 
   * @method POST
   * @path /v1/billing/admin/reload
   */
  async postBillingAdminReload(): Promise<APIResponse<any>> {
    const requestPath = `/v1/billing/admin/reload`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Request tokens allocation (FIN)
   * 
   * @method POST
   * @path /v1/fin/tokens/request
   */
  async postFinTokensRequest(): Promise<APIResponse<any>> {
    const requestPath = `/v1/fin/tokens/request`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Allocate requested tokens (FIN)
   * 
   * @method POST
   * @path /v1/fin/tokens/allocate
   */
  async postFinTokensAllocate(): Promise<APIResponse<any>> {
    const requestPath = `/v1/fin/tokens/allocate`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * Get token request status (FIN)
   * 
   * @method GET
   * @path /v1/fin/tokens/{request_id}
   */
  async getFinTokensRequestId(request_id: string): Promise<APIResponse<any>> {
    const requestPath = `/v1/fin/tokens/{request_id}`.replace(`{request_id}`, encodeURIComponent(String(request_id)));
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Ledger records for case
   * 
   * @method GET
   * @path /v1/ledger/{case_id}/records
   */
  async getLedgerCaseIdRecords(case_id: string): Promise<APIResponse<any>> {
    const requestPath = `/v1/ledger/{case_id}/records`.replace(`{case_id}`, encodeURIComponent(String(case_id)));
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * Reconstruct boundary state
   * 
   * @method POST
   * @path /v1/boundary/reconstruct
   */
  async postBoundaryReconstruct(): Promise<APIResponse<any>> {
    const requestPath = `/v1/boundary/reconstruct`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * FINENITH measure alpha
   * 
   * @method POST
   * @path /v1/fin/alpha/measure
   */
  async postFinAlphaMeasure(): Promise<APIResponse<any>> {
    const requestPath = `/v1/fin/alpha/measure`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * FINENITH simulate strategy
   * 
   * @method POST
   * @path /v1/fin/alpha/simulate
   */
  async postFinAlphaSimulate(): Promise<APIResponse<any>> {
    const requestPath = `/v1/fin/alpha/simulate`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }

  /**
   * FINENITH recent PnL
   * 
   * @method GET
   * @path /v1/fin/alpha/pnl
   */
  async getFinAlphaPnl(): Promise<APIResponse<any>> {
    const requestPath = `/v1/fin/alpha/pnl`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * LEXENITH pilot cases
   * 
   * @method GET
   * @path /v1/lexenith/pilot/cases
   */
  async getLexenithPilotCases(): Promise<APIResponse<any>> {
    const requestPath = `/v1/lexenith/pilot/cases`;
    const options: any = {};
    return this.request("GET", requestPath, options);
  }

  /**
   * LEXENITH pilot feedback
   * 
   * @method POST
   * @path /v1/lexenith/pilot/feedback
   */
  async postLexenithPilotFeedback(): Promise<APIResponse<any>> {
    const requestPath = `/v1/lexenith/pilot/feedback`;
    const options: any = {};
    if (body !== undefined) options.body = body;
    return this.request("POST", requestPath, options);
  }
}

// === EXPORT ===

export default CerteusClient;
