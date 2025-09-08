#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# CERTEUS • Control • PR waiter
# Polls GitHub API for PR check runs until all required checks are SUCCESS.

usage() {
  cat <<'EOF'
Usage: wait-pr-green.sh [--owner OWNER] [--repo REPO] [--pr NUM] [--timeout SEC]

Defaults: --owner CERTEUS --repo certeus, last open PR if --pr omitted.
Requires: GITHUB_TOKEN (env or .control/secrets/GITHUB_TOKEN.txt)
EOF
}

OWNER=CERTEUS
REPO=certeus
PR=""
TIMEOUT=${TIMEOUT:-3600}

while [ $# -gt 0 ]; do
  case "$1" in
    --owner) OWNER="$2"; shift 2 ;;
    --repo)  REPO="$2"; shift 2 ;;
    --pr)    PR="$2";   shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage; exit 2 ;;
  esac
done

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
TOKEN="${GITHUB_TOKEN:-}"
if [ -z "$TOKEN" ] && [ -s "$ROOT_DIR/.control/secrets/GITHUB_TOKEN.txt" ]; then
  TOKEN="$(<"$ROOT_DIR/.control/secrets/GITHUB_TOKEN.txt")"
fi
[ -n "$TOKEN" ] || { echo "GITHUB_TOKEN missing" >&2; exit 2; }

api() {
  local url="$1"
  curl -fsSL -H "Authorization: token $TOKEN" -H 'Accept: application/vnd.github+json' "$url"
}

if [ -z "$PR" ]; then
  PR=$(api "https://api.github.com/repos/$OWNER/$REPO/pulls?state=open&sort=created&direction=desc&per_page=1" | jq -r '.[0].number')
  [ "$PR" != "null" ] || { echo "No open PRs found" >&2; exit 2; }
fi

echo "Waiting for PR #$PR in $OWNER/$REPO to go green…"
start=$(date +%s)
while :; do
  sha=$(api "https://api.github.com/repos/$OWNER/$REPO/pulls/$PR" | jq -r '.head.sha')
  [ -n "$sha" ] && [ "$sha" != "null" ] || { echo "Cannot resolve PR head SHA" >&2; exit 2; }
  runs=$(api "https://api.github.com/repos/$OWNER/$REPO/commits/$sha/check-runs" | jq -r '.check_runs | length')
  success=$(api "https://api.github.com/repos/$OWNER/$REPO/commits/$sha/check-runs" | jq -r '[.check_runs[] | select(.status=="completed") | .conclusion=="success" ] | all')
  echo "- sha=$sha runs=$runs success=$success"
  if [ "$success" = "true" ] && [ "$runs" != "0" ]; then
    echo "All checks green."
    exit 0
  fi
  now=$(date +%s)
  if [ $((now-start)) -ge "$TIMEOUT" ]; then
    echo "Timeout waiting for green checks." >&2
    exit 3
  fi
  sleep 10
done

