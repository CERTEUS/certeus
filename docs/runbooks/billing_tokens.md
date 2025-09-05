# Billing / Cost‑Tokens (W14)

Cel: Zarządzanie budżetem jednostek obliczeniowych per‑tenant.

## Endpoints
- `POST /v1/billing/quota` — ustaw quota dla wskazanego tenant‑a
- `GET /v1/billing/balance` — pobierz saldo tenant‑a z nagłówka `X-Tenant-ID`
- `POST /v1/billing/refund` — zwróć jednostki do budżetu (korekta)
- `POST /v1/billing/allocate` — doładuj saldo bieżącego tenant‑a (PENDING→allocate)

## Przykłady

```
curl -s -X POST http://127.0.0.1:8000/v1/billing/quota \
  -H 'Content-Type: application/json' -d '{"tenant":"acme","units":100}'

curl -s http://127.0.0.1:8000/v1/billing/balance -H 'X-Tenant-ID: acme'

curl -s -X POST http://127.0.0.1:8000/v1/billing/allocate \
  -H 'X-Tenant-ID: acme' -H 'Content-Type: application/json' \
  -d '{"units":25}'

curl -s -X POST http://127.0.0.1:8000/v1/billing/refund \
  -H 'Content-Type: application/json' -d '{"tenant":"acme","units":5}'
```

## Semantyka
- Quota zastępuje dotychczasowy budżet (wartość ≥ 0).
- Balance zwraca aktualne saldo (domyślnie `_DEFAULT_BUDGET=10000` jeśli brak ustawienia).
- Refund i Allocate dodają jednostki do salda; wartości ≤ 0 ignorowane.

