CERTEUS SDK (TypeScript)

- Lekki wrapper `fetch` dla wybranych endpointów API.
- Zero zależności runtime; działa w przeglądarce i Node (z polyfill fetch).
- Kod źródłowy: `src/client.ts` (typy i metody).

Pokryte endpointy:
- GET `/v1/pfs/list` — listowanie zasobów ProofFS
- GET `/v1/pfs/xattrs` — extended attributes
- POST `/v1/proofgate/publish` — publikacja PCO (passthrough z typami)
- GET `/v1/p2p/transport/echo`, POST `/v1/p2p/enqueue`, GET `/v1/p2p/jobs/:id`, GET `/v1/p2p/queue`, POST `/v1/p2p/dequeue_once`

Instalacja (lokalna):
- Node 18+ (browser: nowoczesne przeglądarki)
- Opcjonalnie budowanie paczki: `npm pack` lub `pnpm pack` (jeśli publikujesz)

Użycie:
```ts
import { CerteusClient } from './src/client';

const api = new CerteusClient({ baseUrl: 'http://localhost:8081' });
const list = await api.pfsList('pfs://public');
console.log(list.entries.length);

const res = await api.publish({ pco: { case_id: 'TS-DEMO', risk: { ece: 0.01 } } });
console.log(res.status);
```

Publikacja (paczka):
- Zaktualizuj `package.json` (nazwa, wersja, typy)
- `npm publish --access public` (lub prywatnie w rejestrze firmowym)
