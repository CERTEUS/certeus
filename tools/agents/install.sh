#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# Ensure prerequisites for running headless Codex agents (A0..A9)
# - Portable Node.js if needed
# - Codex CLI installed and logged in

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
NODE_DIR="$ROOT_DIR/.control/.node/node-v22.6.0-linux-x64"

note() { printf "[%s] %s\n" INFO "$*"; }

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

if ! command -v codex >/dev/null 2>&1; then
  note "Installing Codex CLI (@openai/codex)…"
  npm i -g @openai/codex@latest --unsafe-perm --loglevel=error
fi

note "Environment ready. Run: tools/agents/auto_agents.sh or tools/agents/run_all.sh"

