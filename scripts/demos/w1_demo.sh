#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/w1_demo.sh                            |
# | ROLE: Shell script (W1 demo).                               |
# | PLIK: scripts/demos/w1_demo.sh                            |
# | ROLA: Skrypt powłoki (demo W1).                             |
# +-------------------------------------------------------------+
set -euo pipefail

PY=.venv/bin/python
if [[ ! -x "$PY" ]]; then
  echo "Python venv not found: $PY"; exit 1
fi

"$PY" -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000 &
SVR_PID=$!
for _ in {1..80}; do
  if curl -sf http://127.0.0.1:8000/health >/dev/null; then break; fi
  sleep 0.25
done

declare -a ITEMS

do_post() { local path="$1" body="$2"; curl -s -H 'Content-Type: application/json' -d "$body" "http://127.0.0.1:8000${path}"; }
do_get() { local path="$1"; curl -s "http://127.0.0.1:8000${path}"; }

ITEMS+=("$(do_post /v1/chatops/command '{"cmd":"cfe.geodesic","args":{}}')")
ITEMS+=("$(do_post /v1/mailops/ingest '{"mail_id":"DEMO-W1-EMAIL","from_addr":"demo@example.com","to":["ops@example.com"],"subject":"Demo","body_text":"W1 demo","spf":"pass","dkim":"pass","dmarc":"pass","attachments":[]}')")
ITEMS+=("$(do_post /v1/qtm/measure '{"operator":"L","source":"demo","case":"DEMO-W1"}')")
ITEMS+=("$(do_get /v1/qtm/history/DEMO-W1)")
ITEMS+=("$(do_get /v1/cfe/curvature)")
ITEMS+=("$(do_get /v1/lexqft/coverage)")
ITEMS+=("$(do_get /v1/ledger/DEMO-W1/records)")

mkdir -p reports
{
  echo '['
  n=${#ITEMS[@]}
  for ((i=0; i<n; i++)); do
    echo "${ITEMS[$i]}"; if [[ $i -lt $((n-1)) ]]; then echo ','; fi
  done
  echo ']'
} > reports/w1_demo.json

kill "$SVR_PID" 2>/dev/null || true
echo "W1 Demo summary saved to reports/w1_demo.json"

