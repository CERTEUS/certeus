# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/cookbooks/fin_alpha.md                         |
# | ROLE: Project Markdown.                                     |
# | PLIK: docs/cookbooks/fin_alpha.md                         |
# | ROLA: Cookbook FINENITH / Quantum Alpha.                    |
# +-------------------------------------------------------------+

## FINENITH — Quantum Alpha (Cookbook)

Cel: szybki start z `fin.alpha` (pomiar, symulacja, PnL).

### Pomiar sygnałów (R/S)

curl -s -X POST http://127.0.0.1:8000/v1/fin/alpha/measure \
  -H "Content-Type: application/json" \
  -d '{"signals": {"risk_total": 0.1, "sentiment_net": 0.4}}'

Oczekiwane: JSON z `outcome` oraz `p` i nagłówek `X-CERTEUS-PCO-fin.measure`.

### Symulacja strategii

curl -s -X POST http://127.0.0.1:8000/v1/fin/alpha/simulate \
  -H "Content-Type: application/json" \
  -d '{"strategy_id":"qalpha-momentum", "capital": 100000, "horizon_days":30}'

Oczekiwane: metryki `pnl_abs`, `pnl_pct`, `sharpe_stub` + PCO.

### Historia PnL (per-tenant)

curl -s http://127.0.0.1:8000/v1/fin/alpha/pnl

