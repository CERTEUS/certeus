# CERTEUS TypeScript SDK (minimal)

Instalacja (lokalnie z repo):

- Użyj bezpośrednio źródeł (ESM): `import { CerteusClient } from './clients/typescript/certeus-sdk/src/index.js'`

Przykład:

```ts
import { CerteusClient } from './clients/typescript/certeus-sdk/src/index.js'

const cli = new CerteusClient({ baseUrl: 'http://127.0.0.1:8000', tenantId: 'demo' })
console.log(await cli.health())
console.log(await cli.getPublicPCO('case-001'))

// Publish bundle (ack)
const ack = await cli.publishPCOBundle({ rid: 'case-001', smt2_hash: 'a'.repeat(64), lfsc: '(lfsc proof)' })
console.log(ack)
```

Uwagi:
- Metody używają `fetch`; w Node 18+ wbudowane, w starszych dodaj `undici`/`node-fetch`.
- Typy zwrotów: `PublicPCO`, `PublishBundleAck`.
