#!/usr/bin/env bash
set -euo pipefail
# CERTEUS — Bootstrap GitHub self-hosted runner (macOS) + macFUSE
# Requirements: admin shell on macOS host, Homebrew installed (or installable), GH token with repo scope

REPO_SLUG="${REPO_SLUG:-CERTEUS/certeus}"
RUNNER_VERSION="${RUNNER_VERSION:-2.315.0}"
LABELS="${LABELS:-self-hosted,macos,macfuse}"
RUNNER_DIR="${RUNNER_DIR:-$HOME/actions-runner}"

echo "[+] Preparing directory: $RUNNER_DIR"
mkdir -p "$RUNNER_DIR" && cd "$RUNNER_DIR"

echo "[+] Downloading runner v$RUNNER_VERSION"
curl -sSLo actions-runner-osx-x64.tar.gz "https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-osx-x64-${RUNNER_VERSION}.tar.gz"
tar xzf actions-runner-osx-x64.tar.gz

echo "[+] Fetching registration token via gh api"
if ! command -v gh >/dev/null 2>&1; then
  echo "[-] gh not found; installing via brew" >&2
  brew install gh
fi
REG_TOKEN=$(gh api -X POST repos/${REPO_SLUG}/actions/runners/registration-token --jq .token)

echo "[+] Configuring runner (labels: $LABELS)"
./config.sh --url "https://github.com/${REPO_SLUG}" --token "$REG_TOKEN" --labels "$LABELS" --unattended

echo "[+] Installing macFUSE (brew cask)"
brew install --cask macfuse || true
echo "[i] If macFUSE requires Security & Privacy approval, grant it and reboot if necessary."

echo "[+] Installing and starting runner as service"
./svc.sh install
./svc.sh start
echo "[OK] macOS runner ready with labels: $LABELS"

