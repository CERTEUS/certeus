// CERTEUS TypeScript SDK (stub)
// Minimal, browser-friendly wrapper around a few endpoints.

export type PFSListEntry = { uri: string; size: number };
export type PFSListResponse = { prefix: string; entries: PFSListEntry[] };
export type PFSXattrsResponse = { uri: string; xattrs: Record<string, unknown> };

export type PublishRequest = { pco: Record<string, unknown>; budget_tokens?: number; policy?: Record<string, unknown> };
export type PublishResponse = { status: string; pco?: Record<string, unknown>; ledger_ref?: string | null };

export interface CerteusClientOptions {
  baseUrl?: string; // default: '' (relative)
  fetchImpl?: typeof fetch; // custom fetch (node/polyfill)
}

export class CerteusClient {
  private baseUrl: string;
  private f: typeof fetch;
  constructor(opts?: CerteusClientOptions) {
    this.baseUrl = opts?.baseUrl || '';
    this.f = opts?.fetchImpl || fetch;
  }

  private async j<T>(method: string, path: string, body?: unknown): Promise<T> {
    const r = await this.f(this.baseUrl + path, {
      method,
      headers: body ? { 'content-type': 'application/json' } : undefined,
      body: body ? JSON.stringify(body) : undefined,
    });
    if (!r.ok) {
      const t = await r.text();
      throw new Error(`HTTP ${r.status}: ${t}`);
    }
    return (await r.json()) as T;
  }

  // pfs/list
  async pfsList(prefix: string, opts?: { recursive?: boolean; limit?: number; mime?: string }): Promise<PFSListResponse> {
    const q = new URLSearchParams({ prefix });
    if (opts?.recursive) q.set('recursive', 'true');
    if (opts?.limit) q.set('limit', String(opts.limit));
    if (opts?.mime) q.set('mime', String(opts.mime));
    return this.j<PFSListResponse>('GET', `/v1/pfs/list?${q.toString()}`);
  }

  // pfs/xattrs
  async pfsXattrs(uri: string): Promise<PFSXattrsResponse> {
    const q = new URLSearchParams({ uri });
    return this.j<PFSXattrsResponse>('GET', `/v1/pfs/xattrs?${q.toString()}`);
  }

  // proofgate/publish
  async publish(req: PublishRequest): Promise<PublishResponse> {
    return this.j<PublishResponse>('POST', '/v1/proofgate/publish', req);
  }
}

