# Onboarding (First 30 Minutes)

> Cel: uruchom lokalnie ProofGate/Boundary, zrób jeden PCO, zobacz wpis w Ledger.

## DEV

```bash
uv venv && source .venv/bin/activate  # Windows: .\.venv\Scripts\Activate.ps1
uv pip install -r requirements.txt
docker compose -f infra/docker-compose.local-infra.yml up -d           # postgres/redis/minio
docker compose -f infra/docker-compose.dev.yml up -d --build proofgate boundary

# zdrowie
curl -s http://localhost:8081/healthz | jq .
```

## SRE

```bash
kubectl apply -f infra/k8s/core.yaml
kubectl apply -f infra/k8s/services.yaml
kubectl apply -f infra/k8s/ingress.yaml
docker compose -f infra/docker-compose.monitoring.yml up -d
```

## AUDYTOR

```bash
# przykładowe polecenia - stuby
curl -s http://localhost:8081/v1/ledger/CER-DEMO | jq . || true
```

## LEGAL/PM

- Otwórz README i Manifest.
- Social preview: ustaw `docs/assets/brand/certeus-og.png`.
