# Deployment

Deploy CERTEUS to Kubernetes via Helm or run locally via Docker Compose.

## Helm (Kubernetes)

```bash
helm repo add certeus https://charts.certeus.io
helm install certeus certeus/certeus \
  --set api.image.tag=v1.5.0 \
  --set security.strictProofOnly=true

kubectl get pods -n certeus
kubectl logs -f deployment/certeus-api
```

## Docker Compose (Local)

```yaml
version: '3.8'
services:
  certeus-api:
    image: ghcr.io/certeus/certeus:latest
    ports: ["8000:8000"]
    environment:
      - STRICT_PROOF_ONLY=1
      - OBSERVABILITY_ENABLED=1
  certeus-ui:
    image: ghcr.io/certeus/certeus-ui:latest
    ports: ["8080:80"]
  prometheus:
    image: prom/prometheus
    ports: ["9090:9090"]
  grafana:
    image: grafana/grafana
    ports: ["3000:3000"]
```

## Production Hardening

```bash
export STRICT_PROOF_ONLY=1
export PQ_CRYPTO_ENABLED=1
export TEE_ATTESTATION_REQUIRED=1
export RATE_LIMIT_PER_MIN=100
export CORS_ALLOW_ORIGINS="https://yourdomain.com"
```

See also: [SECURITY.md](SECURITY.md), [observability/quickstart.md](observability/quickstart.md).

