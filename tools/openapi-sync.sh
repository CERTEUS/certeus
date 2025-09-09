#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# Verify or sync OpenAPI between Control/docs and CERTEUS/docs.
# Usage:
#   tools/openapi-sync.sh verify
#   tools/openapi-sync.sh sync [--from control|certeus]

MODE=${1:-verify}
FROM=${2:---from certeus}

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
CTL="$ROOT_DIR/docs/api/openapi.yaml"
CER="$ROOT_DIR/certeus/docs/openapi/certeus.v1.yaml"

case "$MODE" in
  verify)
    if diff -u "$CTL" "$CER" >/dev/null; then
      echo "OpenAPI: in sync"
      exit 0
    else
      echo "OpenAPI: mismatch between $CTL and $CER" >&2
      diff -u "$CTL" "$CER" || true
      exit 3
    fi
    ;;
  sync)
    if [[ "$FROM" =~ control ]]; then
      cp -f "$CTL" "$CER"
      echo "Synced: control -> certeus"
    else
      cp -f "$CER" "$CTL"
      echo "Synced: certeus -> control"
    fi
    ;;
  *)
    echo "Usage: $0 verify|sync [--from control|certeus]" >&2
    exit 2
    ;;
esac

