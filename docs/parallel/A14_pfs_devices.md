# A14 — PFS/Devices stability

Scope:
- services/api_gateway/routers/pfs*.py, devices.py

Tasks:
- [x] DHT: TTL=0 wyklucza węzły; capacity-aware assign (load/cap)
- [x] PFS sign/verify: lepsze komunikaty błędów i testy skrajne
- [x] Devices: nagłówki TTL/idempotency, metryki; brak regresji kontraktu

DOD:
- [x] tests/services dla PFS/Devices zielone, brak flakiness (property tests)

Do not touch:
- billing, openapi docs (poza koniecznymi dopasowaniami testów usług)
