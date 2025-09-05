# A13 — API contract parity (op-id, docs)

Scope:
- services/api_gateway/routers/billing*.py (unikalne operation_id)
- docs/api/openapi.yaml (parytet runtime↔docs)
- scripts/contracts/** (tylko pod test kontraktu)

Tasks:
- [ ] Zunifikować operation_id (uniknąć duplikatów fin_* vs billing_*)
- [ ] Zaktualizować docs/api/openapi.yaml do runtime (bez wycieku ścieżek niezaimplementowanych)
- [ ] Spectral lint: brak errorów (warningi akceptowalne)

DOD:
- [ ] Test kontraktu i openapi-pages zielone
- [ ] Brak duplikatów operation_id w logach CI

Do not touch:
- PFS/Devices/LexQFT; tests tylko kontraktowe
