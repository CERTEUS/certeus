/*
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: clients/typescript/certeus-sdk/src/index.ts          |
| ROLE: TypeScript SDK client                                 |
| PLIK: clients/typescript/certeus-sdk/src/index.ts          |
| ROLA: Klient SDK w TypeScript                               |
+-------------------------------------------------------------+
*/

export type Json = Record<string, unknown>;

export interface PublishBundleRequest {
  rid: string;
  smt2_hash: string;
  lfsc: string;
  drat?: string | null;
  merkle_proof?: Array<{ sibling: string; dir: 'L' | 'R' }> | { path: Array<{ sibling: string; dir: 'L' | 'R' }> } | null;
  smt2?: string | null;
}

export interface PublicPCO {
  rid: string;
  smt2_hash: string;
  lfsc: string;
  drat?: string;
  merkle_proof: Array<{ sibling: string; dir: 'L' | 'R' }>;
  signature: string;
}

export interface PublishBundleAck {
  ok: boolean;
  rid: string;
  digest_hex: string;
  signature: string;
  public_path: string;
}

export interface CerteusOptions {
  baseUrl?: string;
  tenantId?: string;
  timeoutMs?: number;
}

export class CerteusClient {
  baseUrl: string;
  tenantId?: string;
  timeoutMs: number;

  constructor(opts: CerteusOptions = {}) {
    this.baseUrl = (opts.baseUrl || "http://127.0.0.1:8000").replace(/\/$/, "");
    this.tenantId = opts.tenantId;
    this.timeoutMs = opts.timeoutMs ?? 15000;
  }

  private url(path: string): string {
    return `${this.baseUrl}${path}`;
  }

  private headers(): HeadersInit {
    const h: HeadersInit = { "Content-Type": "application/json" };
    if (this.tenantId) (h as Record<string, string>)["X-Tenant-ID"] = this.tenantId;
    return h;
  }

  async openapi(): Promise<Json> {
    const r = await fetch(this.url("/openapi.json"));
    if (!r.ok) throw new Error(`/openapi.json => ${r.status}`);
    return (await r.json()) as Json;
  }

  async health(): Promise<Json> {
    const r = await fetch(this.url("/health"));
    if (!r.ok) throw new Error(`/health => ${r.status}`);
    return (await r.json()) as Json;
  }

  async getPublicPCO(caseId: string): Promise<PublicPCO> {
    const r = await fetch(this.url(`/pco/public/${encodeURIComponent(caseId)}`));
    if (!r.ok) throw new Error(`/pco/public => ${r.status}`);
    return (await r.json()) as PublicPCO;
  }

  async publishPCOBundle(payload: PublishBundleRequest): Promise<PublishBundleAck> {
    const r = await fetch(this.url(`/v1/pco/bundle`), {
      method: 'POST',
      headers: { 'Content-Type': 'application/json', ...(this.tenantId ? { 'X-Tenant-ID': this.tenantId } : {}) },
      body: JSON.stringify(payload),
    });
    if (!r.ok) throw new Error(`/v1/pco/bundle => ${r.status}`);
    return (await r.json()) as PublishBundleAck;
  }

  async analyze(caseId: string, file: Blob, filename = 'document.pdf'): Promise<Json> {
    const fd = new FormData();
    fd.append('file', file, filename);
    const r = await fetch(this.url(`/v1/analyze?case_id=${encodeURIComponent(caseId)}`), {
      method: 'POST',
      body: fd,
      headers: this.tenantId ? { 'X-Tenant-ID': this.tenantId } : undefined,
    });
    if (!r.ok) throw new Error(`/v1/analyze => ${r.status}`);
    return (await r.json()) as Json;
  }
}

export default CerteusClient;
