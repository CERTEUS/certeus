#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: examples/fin_alpha_curl.sh                           |
# | ROLE: Project script.                                        |
# | PLIK: examples/fin_alpha_curl.sh                           |
# | ROLA: cURL demo dla FINENITH / Quantum Alpha.                |
# +-------------------------------------------------------------+

set -euo pipefail

base="${BASE_URL:-http://127.0.0.1:8000}"

echo "# Measure"
curl -s -X POST "$base/v1/fin/alpha/measure" -H 'Content-Type: application/json' \
  -d '{"signals": {"risk_total": 0.1, "sentiment_net": 0.4}}' | jq .

echo "# Simulate"
curl -s -X POST "$base/v1/fin/alpha/simulate" -H 'Content-Type: application/json' \
  -d '{"strategy_id":"qalpha-momentum","capital":100000,"horizon_days":30}' | jq .

echo "# PnL"
curl -s "$base/v1/fin/alpha/pnl" | jq .

