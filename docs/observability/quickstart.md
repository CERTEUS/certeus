# Observability – Quickstart (OTEL/Prometheus)

- Export OTLP locally: `python scripts/otel/mock_otlp.py` (CI uses this mock receiver).
- Start API with metrics: `uvicorn services.api_gateway.main:app` then visit `/metrics`.
- Prometheus scrape: use `infra/docker-compose.monitoring.yml` or point Prometheus to the API’s `/metrics` endpoint.
- Grafana: import dashboards from `observability/grafana/*.json`.
- Dashboards preview: see `observability/preview/`.

Per-tenant SLO (W16):
- Użyj nagłówka `X-Tenant-ID` w żądaniach, aby metryki miały etykietę `tenant`.
- p95 per-tenant: `histogram_quantile(0.95, sum(rate(certeus_http_request_duration_ms_tenant_bucket[5m])) by (le, tenant))`.
- Error-rate per-tenant: `sum(rate(certeus_http_requests_total{status=~"5.."}[5m])) by (tenant) / sum(rate(certeus_http_requests_total[5m])) by (tenant)`.

Tips:
- Set `OTEL_ENABLED=1` to enable tracing in CI/local demos.
- Quick perf: `python scripts/perf/quick_bench.py` writes `out/perf_bench.json` and CI publishes p95.
