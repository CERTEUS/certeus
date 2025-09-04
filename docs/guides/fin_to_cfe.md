#!/usr/bin/env markdown

# FIN → CFE (Guide)

Cel: Płynny przepływ sygnałów FIN (risk/sentiment) do warstwy CFE (lensing), z przykładami API i cURL.

## Przepływ
- Zbieramy sygnały FIN (`risk`, `sentiment`, inne).
- Wołamy `POST /v1/cfe/lensing/from_fin` z `signals` i opcjonalnym `seed`.
- Odbieramy `lensing_map` (precedens → waga) i `critical_precedents`.
- UI (Geometry) odświeża panel Lensing i umożliwia filtrowanie (K_/III_/SN_).

## API
- `POST /v1/cfe/lensing/from_fin`
- `POST /v1/cfe/cache/warm` — rozgrzanie cache (opcjonalne pre-warm dla znanych spraw).
- `GET /v1/cfe/lensing?case_id=...` — odczyt lensingu per case.

## cURL
- Lensing z FIN:
```
curl -s -X POST http://127.0.0.1:8000/v1/cfe/lensing/from_fin \
 -H 'Content-Type: application/json' \
 -d '{"signals":{"risk":0.2,"sentiment":0.6},"seed":"FIN-CASE-1"}' | jq .
```
- Warm cache (lista spraw):
```
curl -s -X POST http://127.0.0.1:8000/v1/cfe/cache/warm \
 -H 'Content-Type: application/json' \
 -d '["LEX-001","LEX-002"]' | jq .
```
- Lensing per case:
```
curl -s "http://127.0.0.1:8000/v1/cfe/lensing?case_id=LEX-001" | jq .
```

## Uwagi jakościowe (enterprise)
- Deterministyczność: lensing z FIN jest deterministyczny względem `seed` oraz stabilny numerycznie.
- Telemetria: rekomendowane śledzenie korelacji FIN↔CFE w metrykach (np. rozszerzalne przez `monitoring/metrics_slo.py`).
- Cache: GET’y opatrzone `Cache-Control: public, max-age=<ttl>`, mutacje `no-store`.
- PCO: helper dodaje nagłówek `X-CERTEUS-PCO-cfe.lensing_from_fin` ze `score`.
