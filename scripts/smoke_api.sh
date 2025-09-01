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

