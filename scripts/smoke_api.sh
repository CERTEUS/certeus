#!/usr/bin/env bash
# CERTEUS — Simple API smoke test (Linux/macOS)

set -euo pipefail

if [[ -f ./scripts/dev_env.sh ]]; then
  # shellcheck disable=SC1091
  source ./scripts/dev_env.sh
fi

PY=.venv/bin/python
[[ -x "$PY" ]] || { echo "Python venv not found: $PY"; exit 1; }

function start_server() {
  $PY -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000 &
  SVR_PID=$!
  for _ in {1..80}; do
    if curl -sf http://127.0.0.1:8000/health >/dev/null; then break; fi
    sleep 0.25
  done
}

function stop_server() {
  [[ -n "${SVR_PID:-}" ]] && kill "$SVR_PID" 2>/dev/null || true
}

function hit() {
  local method=$1 path=$2 body=${3:-}
  local url="http://127.0.0.1:8000${path}"
  if [[ "$method" == GET ]]; then
    code=$(curl -s -o /dev/null -w "%{http_code}" "$url")
    echo "[GET] $path => $code"
  else
    code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -X POST -d "$body" "$url")
    echo "[POST] $path => $code"
  fi
}

trap stop_server EXIT
start_server

hit GET /health
hit GET /
hit GET /metrics
hit GET /.well-known/jwks.json
hit GET /v1/packs/
hit POST /v1/fin/alpha/measure '{"signals":{"risk":0.10,"sentiment":0.55}}'
hit GET /v1/fin/alpha/uncertainty
hit GET /v1/fin/alpha/entanglements
curl -s -o /dev/null -w "[POST] /v1/cfe/geodesic => %{http_code}\n" -H 'Content-Type: application/json' -d '{"case":"CER-SMOKE","facts":{},"norms":{}}' http://127.0.0.1:8000/v1/cfe/geodesic
curl -s -o /dev/null -w "[POST] /v1/cfe/horizon => %{http_code}\n" -H 'Content-Type: application/json' -d '{}' http://127.0.0.1:8000/v1/cfe/horizon
hit GET /v1/cfe/lensing
curl -s -o /dev/null -w "[POST] /v1/qtm/init_case => %{http_code}\n" -H 'Content-Type: application/json' -d '{"basis":["ALLOW","DENY","ABSTAIN"]}' http://127.0.0.1:8000/v1/qtm/init_case
curl -s -o /dev/null -w "[POST] /v1/qtm/measure => %{http_code}\n" -H 'Content-Type: application/json' -d '{"operator":"W","source":"ui"}' http://127.0.0.1:8000/v1/qtm/measure
curl -s -o /dev/null -w "[POST] /v1/qtm/commutator => %{http_code}\n" -H 'Content-Type: application/json' -d '{"A":"X","B":"Y"}' http://127.0.0.1:8000/v1/qtm/commutator
curl -s -o /dev/null -w "[POST] /v1/qtm/find_entanglement => %{http_code}\n" -H 'Content-Type: application/json' -d '{"variables":["A","B"]}' http://127.0.0.1:8000/v1/qtm/find_entanglement
curl -s -o /dev/null -w "[POST] /v1/devices/horizon_drive/plan => %{http_code}\n" -H 'Content-Type: application/json' -d '{}' http://127.0.0.1:8000/v1/devices/horizon_drive/plan
curl -s -o /dev/null -w "[POST] /v1/devices/qoracle/expectation => %{http_code}\n" -H 'Content-Type: application/json' -d '{"objective":"maximize fairness","constraints":{}}' http://127.0.0.1:8000/v1/devices/qoracle/expectation
curl -s -o /dev/null -w "[POST] /v1/devices/entangle => %{http_code}\n" -H 'Content-Type: application/json' -d '{"variables":["RISK","SENTIMENT"],"target_negativity":0.1}' http://127.0.0.1:8000/v1/devices/entangle
curl -s -o /dev/null -w "[POST] /v1/devices/chronosync/reconcile => %{http_code}\n" -H 'Content-Type: application/json' -d '{"coords":{"t":0},"pc_delta":{}}' http://127.0.0.1:8000/v1/devices/chronosync/reconcile
curl -s -o /dev/null -w "[POST] /v1/ethics/equity_meter => %{http_code}\n" -H 'Content-Type: application/json' -d '{"distribution_a":[0.2,0.8],"distribution_b":[0.5,0.5]}' http://127.0.0.1:8000/v1/ethics/equity_meter
curl -s -o /dev/null -w "[POST] /v1/ethics/double_verdict => %{http_code}\n" -H 'Content-Type: application/json' -d '{"W_litera":"ALLOW","T_telos":"TRUTH","rationale":"smoke"}' http://127.0.0.1:8000/v1/ethics/double_verdict
curl -s -o /dev/null -w "[POST] /v1/chatops/command => %{http_code}\n" -H 'Content-Type: application/json' -d '{"cmd":"cfe.geodesic","args":{}}' http://127.0.0.1:8000/v1/chatops/command

# Ledger
curl -s -o /dev/null -w "[POST] /v1/ledger/record-input => %{http_code}\n" -H 'Content-Type: application/json' -d '{"case_id":"CER-1","document_hash":"sha256:0000000000000000000000000000000000000000000000000000000000000000"}' http://127.0.0.1:8000/v1/ledger/record-input
hit GET /v1/ledger/CER-1/records
hit GET /v1/ledger/CER-1/prove

# PCO bundle + public verify
curl -s -o /dev/null -w "[POST] /v1/pco/bundle => %{http_code}\n" -H 'Content-Type: application/json' -d '{"rid":"RID-SMOKE-1","smt2_hash":"0000000000000000000000000000000000000000000000000000000000000000","lfsc":"(lfsc proof)","drat":"p drat","merkle_proof":[]}' http://127.0.0.1:8000/v1/pco/bundle
hit GET /pco/public/RID-SMOKE-1

# Preview upload
tmp_txt=$(mktemp)
echo 'hello world' > "$tmp_txt"
code=$(curl -s -o /dev/null -w "%{http_code}" -F "file=@$tmp_txt;type=text/plain" http://127.0.0.1:8000/v1/preview)
echo "[POST] /v1/preview => $code"

# Ingest/analyze (PDF)
tmp_pdf=$(mktemp --suffix .pdf)
printf '%%PDF-1.4\n1 0 obj<<>>endobj\ntrailer<<>>\n%%EOF' > "$tmp_pdf"
code=$(curl -s -o /dev/null -w "%{http_code}" -F "file=@$tmp_pdf;type=application/pdf" http://127.0.0.1:8000/v1/ingest)
echo "[POST] /v1/ingest => $code"
code=$(curl -s -o /dev/null -w "%{http_code}" -F "file=@$tmp_pdf;type=application/pdf" 'http://127.0.0.1:8000/v1/analyze?case_id=CER-1')
echo "[POST] /v1/analyze => $code"

# Source cache (file://)
tmp_src=$(mktemp)
echo 'source-cache' > "$tmp_src"
curl -s -o /dev/null -w "[POST] /v1/sources/cache => %{http_code}\n" -H 'Content-Type: application/json' -d '{"uri":"file:///'"$tmp_src"'"}' http://127.0.0.1:8000/v1/sources/cache

# Publish
curl -s -o /dev/null -w "[POST] /defx/reason => %{http_code}\n" -H 'Content-Type: application/json' -H 'X-Norm-Pack-ID: norms.default' -H 'X-Jurisdiction: PL' -d '{"tenant":"anon","sla":"basic"}' http://127.0.0.1:8000/defx/reason
