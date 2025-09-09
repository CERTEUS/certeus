# Monitoring & Observability

Key metrics, tracing, and dashboards for operating CERTEUS.

## Metrics & SLOs

- Prometheus metrics and recording rules
- SLO examples and alerting policies

Example queries:

```promql
# API Response Time (p95)
histogram_quantile(0.95, rate(certeus_http_request_duration_ms_bucket[5m]))

# Error Rate
rate(certeus_http_requests_total{status=~"5.."}[5m]) / rate(certeus_http_requests_total[5m])

# Proof Verification Success Rate
rate(certeus_proof_verifications_total{status="success"}[5m])
```

- Dashboards: Grafana JSON exports (internal)
- Tracing: OpenTelemetry + Jaeger

## Quickstart

- See: [observability/quickstart.md](observability/quickstart.md)
- Related runbooks:
  - [runbooks/gauge-drift.md](runbooks/gauge-drift.md)
  - [runbooks/ebpf_telemetry.md](runbooks/ebpf_telemetry.md)
  - [runbooks/w10_sre.md](runbooks/w10_sre.md)

