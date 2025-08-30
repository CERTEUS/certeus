# SLA / SLO

- **SLO API**: p95 latencja <= 250 ms (intra-DC), p99 błędów <= 0.5% / 30d
- **Error Budget**: 0.5% na 30 dni
- **Alerting**: multi-burn-rate (2%/1h, 5%/6h)

## Priorytety

- P1: ProofGate/Boundary niedostępne
- P2: Degradacja p95 > SLO 2x
- P3: Pojedyncze endpointy/lokacje

## RTO/RPO

- RTO: 30 min, RPO: 5 min (Boundary + Ledger snapshot)
