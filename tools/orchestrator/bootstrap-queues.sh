#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# Seed P2P device queues with demo jobs via API.
# Usage: tools/orchestrator/bootstrap-queues.sh [--base URL]

BASE="${1:-}"
if [[ "$BASE" == "--base" ]]; then
  BASE="$2"; shift 2 || true
fi
BASE="${BASE:-http://localhost:8081}"

echo "Bootstrapping queues at: $BASE"

payload() {
  cat <<'JSON'
{"payload":{"demo":true,"ts":0}}
JSON
}

for dev in hde qoracle entangler chronosync; do
  echo "- Enqueue device=$dev"
  curl -fsSL -H 'content-type: application/json' -X POST \
    "$BASE/v1/p2p/enqueue" -d "$(jq -cn --arg d "$dev" '{ device: $d, payload: {demo:true}}')" >/dev/null
done

echo "Done. Use GET $BASE/v1/p2p/queue to inspect."

