# W1 Demo — Stabilizacja i Telemetria Core

Cel tygodnia: uruchomić bramki jakości i kontrakty; wystawić realną telemetrię CFE oraz podstawowe smoki.

Szybkie kroki (lokalnie)
- Lint: `python -m ruff check . --fix && python -m ruff format .`
- Testy: `mkdir -p reports && python -m pytest -q --junitxml=reports/junit.xml`
- Serwer: `python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`

Endpoints (smoke)
- CFE Curvature: `GET /v1/cfe/curvature?case_id=LEX-001` → `{kappa_max}` (deterministyczne per case)
- CFE Geodesic: `POST /v1/cfe/geodesic {case}` → `{path, geodesic_action}` (PCO header)
- CFE Horizon: `POST /v1/cfe/horizon {case, lock}` → `{locked, horizon_mass}` (PCO header)
- CFE Lensing: `GET /v1/cfe/lensing?case_id=LEX-001` → `{lensing_map, critical_precedents}`
- LexQFT Coverage: `GET /v1/lexqft/coverage` → `{coverage_gamma}`
- LexQFT Tunnel (WKB): `POST /v1/lexqft/tunnel {evidence_energy, barrier_model}`
- Health & Metrics: `GET /health`, `GET /metrics`, `GET /openapi.json`

UI (Geometry)
- `http://127.0.0.1:8000/app/public/geometry.html` — heatmapa Ricciego, geodezyjna i lock (curvature odświeżany po akcji).

Dowód i metryki
- PCO: nagłówki `X-CERTEUS-PCO-cfe.*`, `X-CERTEUS-PCO-qlaw.tunneling.*`; zapisy do Ledger (hashy).
- Prometheus: `certeus_cfe_kappa_max`, `certeus_http_request_duration_ms*`.

Uwagi operacyjne
- Rate‑limit GET `/health` sterowany `RATE_LIMIT_PER_MIN` (testy: zielone).
- OpenAPI cache w gateway przyspiesza `/openapi.json`.

