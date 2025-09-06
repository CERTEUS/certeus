#!/usr/bin/env bash
set -euo pipefail

ENVF=${1:-.env.macos-runner}
if [[ -f "$ENVF" ]]; then
  # shellcheck disable=SC1090
  source "$ENVF"
else
  echo "[!] Brak pliku $ENVF. Utwórz go lub przekaż ścieżkę jako 1. argument." >&2
  echo "    Szkielet został przygotowany w repo (plik .env.macos-runner)." >&2
  exit 1
fi

echo "[i] Uruchamiam scripts/agent_up.sh z ustawionymi zmiennymi..."
exec bash "$(dirname "$0")/agent_up.sh"

