#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
PID_DIR="$ROOT_DIR/.control/.tmp/agents"

if [ ! -d "$PID_DIR" ]; then
  echo "No PID directory: $PID_DIR" >&2
  exit 0
fi

stopped=0
for f in "$PID_DIR"/*.pid; do
  [ -e "$f" ] || continue
  pid=$(cat "$f" 2>/dev/null || true)
  if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
    kill "$pid" || true
    echo "Stopped PID $pid ($f)"
    stopped=$((stopped+1))
  fi
  rm -f "$f"
done
echo "Done. Stopped: $stopped"

