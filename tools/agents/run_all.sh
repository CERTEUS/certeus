#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# Start A0..A9 Codex CLI sessions headless using prompts in .control/plans/agents/
# Requires: Codex CLI logged in; CODEX_HOME set; working dir = repo root (control)

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
PROMPTS="$ROOT_DIR/.control/plans/agents"
OUTDIR="$ROOT_DIR/.control/.tmp/agents"
mkdir -p "$OUTDIR"

start_one() {
  local i="$1"
  local p="$PROMPTS/A${i}.prompt.md"
  local log="$OUTDIR/A${i}_live.jsonl"
  local pidf="$OUTDIR/A${i}_live.pid"
  [ -s "$p" ] || { echo "[WARN] Missing prompt $p" >&2; return 0; }
  # Run in certeus workspace, workspace-write sandbox
  # Use stdbuf for line-buffered streaming and nohup for daemonization
  nohup bash -lc "stdbuf -oL -eL cat '$p' | codex exec -C certeus -s workspace-write --json -" \
    >"$log" 2>&1 & echo $! >"$pidf"
  echo "[A${i}] PID $(cat "$pidf") → $log"
}

echo "[INFO] Starting A0..A9 sessions…"
for i in 0 1 2 3 4 5 6 7 8 9; do
  start_one "$i"
done

echo "[INFO] To watch: tail -f $OUTDIR/A*_live.jsonl"

