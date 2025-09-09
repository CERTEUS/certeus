#!/usr/bin/env bash
set -euo pipefail

# Inicjalizacja lokalnego "miejsca" na sekrety i sprawdzenie zależności.
# Nie zapisuje nic do repozytorium poza .gitignore (już istnieje).
# Użycie:
#   tools/setup.sh               # utworzy .control/ z prawami 700
#   tools/setup.sh --write-key   # zapisze GH_APP_PRIVATE_KEY do .control/*.pem

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
get_repo_root() {
  if command -v git >/dev/null 2>&1; then
    if git -C "${SCRIPT_DIR}" rev-parse --show-toplevel >/dev/null 2>&1; then
      git -C "${SCRIPT_DIR}" rev-parse --show-toplevel
      return
    fi
  fi
  (cd "${SCRIPT_DIR}/../.." 2>/dev/null && pwd) || (cd "${SCRIPT_DIR}/.." 2>/dev/null && pwd)
}
REPO_ROOT="$(get_repo_root)"

WRITE_KEY=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --write-key) WRITE_KEY=1; shift ;;
    -h|--help) echo "Użycie: $0 [--write-key]"; exit 0 ;;
    *) echo "Nieznana opcja: $1" >&2; exit 2 ;;
  esac
done

mkdir -p "${REPO_ROOT}/.control"
chmod 700 "${REPO_ROOT}/.control" || true

if [[ $WRITE_KEY -eq 1 ]]; then
  mkdir -p "${REPO_ROOT}/.control/keys"
  key_path="${REPO_ROOT}/.control/keys/github-app-private-key.pem"
  umask 077
  if [[ -n "${GH_APP_PRIVATE_KEY_B64:-}" ]]; then
    printf '%s' "${GH_APP_PRIVATE_KEY_B64}" | tr -d '\n' | base64 -d >"${key_path}"
    echo "Zapisano klucz z GH_APP_PRIVATE_KEY_B64 do ${key_path}"
  elif [[ -n "${GH_APP_PRIVATE_KEY:-}" ]]; then
    printf '%s' "${GH_APP_PRIVATE_KEY}" | sed 's/\\n/\n/g' >"${key_path}"
    echo "Zapisano klucz z GH_APP_PRIVATE_KEY do ${key_path}"
  else
    echo "Brak GH_APP_PRIVATE_KEY(_B64) w env. Pomiń --write-key jeśli chcesz wkleić ręcznie." >&2
  fi
fi

echo "Utworzono .control/ i sprawdzono podstawy."
