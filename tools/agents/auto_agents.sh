#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# CERTEUS • Control • Orchestrator
# Launches 10 Codex CLI headless sessions (A0..A9) with per‑agent prompts.
# Preconditions:
#  - Codex CLI logged in (codex login status → Logged in)
#  - Git remotes set for both this repo (control) and submodule (certeus)
#  - GITHUB_TOKEN present (file .control/secrets/GITHUB_TOKEN.txt or env)

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
PROMPTS_DIR="$ROOT_DIR/.control/plans/agents"
LOG_DIR="$ROOT_DIR/.control/.tmp/agents"
NODE_DIR="$ROOT_DIR/.control/.node/node-v22.6.0-linux-x64"

mkdir -p "$LOG_DIR"

note() { printf "[%s] %s\n" "INFO" "$*"; }
die()  { printf "[%s] %s\n" "ERR"  "$*" >&2; exit 2; }

# 1) Ensure Node.js and npm (portable, user‑local)
if ! command -v node >/dev/null 2>&1; then
  if [ ! -x "$NODE_DIR/bin/node" ]; then
    note "Downloading portable Node.js (v22.6.0)…"
    mkdir -p "${NODE_DIR%/*}"
    curl -fsSL https://nodejs.org/dist/v22.6.0/node-v22.6.0-linux-x64.tar.xz -o "$ROOT_DIR/.control/.node/node.tar.xz"
    tar -xJf "$ROOT_DIR/.control/.node/node.tar.xz" -C "$ROOT_DIR/.control/.node/"
    rm -f "$ROOT_DIR/.control/.node/node.tar.xz"
  fi
  export PATH="$NODE_DIR/bin:$PATH"
fi

# 2) Ensure Codex CLI
if ! command -v codex >/dev/null 2>&1; then
  note "Installing Codex CLI (@openai/codex)…"
  npm i -g @openai/codex@latest --unsafe-perm --loglevel=error
fi

# 3) Check login
if codex login status | grep -qi "Not logged in"; then
  die "Codex CLI is NOT logged in. Run: export PATH=\"$NODE_DIR/bin:\$PATH\"; codex login"
fi

# 4) Configure Git credentials from token (if available)
GITHUB_TOKEN_ENV="${GITHUB_TOKEN:-}"
if [ -z "$GITHUB_TOKEN_ENV" ] && [ -s "$ROOT_DIR/.control/secrets/GITHUB_TOKEN.txt" ]; then
  GITHUB_TOKEN_ENV="$(<"$ROOT_DIR/.control/secrets/GITHUB_TOKEN.txt")"
fi
if [ -n "$GITHUB_TOKEN_ENV" ]; then
  note "Configuring Git credential helper (store)…"
  git config --global credential.helper store
  credfile="$HOME/.git-credentials"
  proto_line="https://x-access-token:${GITHUB_TOKEN_ENV}@github.com"
  grep -qxF "$proto_line" "$credfile" 2>/dev/null || echo "$proto_line" >> "$credfile"
else
  note "WARNING: No GITHUB_TOKEN provided. Push/PR may fail."
fi

# 5) Launch agents A0..A9 (headless)
note "Launching headless Codex agents from $PROMPTS_DIR …"
for i in 0 1 2 3 4 5 6 7 8 9; do
  pfile="$PROMPTS_DIR/A${i}.prompt.md"
  [ -s "$pfile" ] || die "Missing prompt: $pfile"
  log="$LOG_DIR/A${i}.log"
  # Root of work: submodule certeus
  (
    cd "$ROOT_DIR" && \
    set -o pipefail && \
    cat "$pfile" | stdbuf -oL -eL codex exec -C certeus -s workspace-write - --json \
      --output-last-message "$LOG_DIR/A${i}.last.json" 2>&1 | tee "$log"
  ) &
  echo $! >"$LOG_DIR/A${i}.pid"
  note "A${i} → PID $(cat "$LOG_DIR/A${i}.pid") • log: $log"
done

note "All agents started. Monitor logs in $LOG_DIR or run: tail -f $LOG_DIR/A*.log"
note "To wait for PR checks, use: tools/remote-bot/wait-pr-green.sh"

# 6) Start green watcher (GitHub PR checks)
python3 "$ROOT_DIR/tools/agents/watch_all_green.py" --owner CERTEUS --repo certeus --interval 30 --comment 1 \
  >"$LOG_DIR/watch.log" 2>&1 &
echo $! >"$LOG_DIR/watch.pid"
note "Green watcher PID $(cat "$LOG_DIR/watch.pid") • log: $LOG_DIR/watch.log"
