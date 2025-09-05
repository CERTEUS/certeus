# CERTEUS SDK (TypeScript)

Minimalny klient TS dla CERTEUS (fetch).

Użycie (Node 18+ / Deno / przeglądarka):

```ts
import { CerteusClient } from "../clients/typescript/certeus-sdk/src/index.js";

const cli = new CerteusClient({ baseUrl: "http://127.0.0.1:8000", tenantId: "demo" });
const info = await cli.openapi();
console.log(info.info);

const health = await cli.health();
console.log(health);
```

