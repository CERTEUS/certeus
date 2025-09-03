#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../clients/python/certeus_sdk"
python -m pip install -U twine >/dev/null
if [ ! -d dist ]; then
  echo "dist/ not found; building..." >&2
  python -m pip install -U build >/dev/null
  python -m build
fi
# Requires environment variables TWINE_USERNAME / TWINE_PASSWORD or .pypirc
twine upload dist/*

