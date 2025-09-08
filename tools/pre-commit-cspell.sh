#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# Run cspell on Markdown files if available. Meant for pre-commit.

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
CSPELL=$(command -v cspell || true)

if [ -z "$CSPELL" ]; then
  echo "[cspell] not installed — skipping" >&2
  exit 0
fi

shopt -s nullglob globstar
files=(**/*.md)
ignore_prefixes=(".control/" ".git/" "certeus/.hypothesis/" "certeus/.pytest_cache/")
args=("--no-progress" "--config" "$ROOT_DIR/.cspell.json")

exit_code=0
for f in "${files[@]}"; do
  # Skip ignored prefixes
  skip=0
  for p in "${ignore_prefixes[@]}"; do
    [[ "$f" == $p* ]] && { skip=1; break; }
  done
  [ $skip -eq 1 ] && continue
  "$CSPELL" "${args[@]}" "$f" || exit_code=1
done

exit $exit_code
