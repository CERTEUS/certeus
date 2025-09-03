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

  async getPublicPCO(caseId: string): Promise<Json> {
    const r = await fetch(this.url(`/pco/public/${encodeURIComponent(caseId)}`));
    if (!r.ok) throw new Error(`/pco/public => ${r.status}`);
    return (await r.json()) as Json;
  }
}

export default CerteusClient;

