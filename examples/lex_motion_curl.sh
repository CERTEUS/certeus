#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: examples/lex_motion_curl.sh                          |
# | ROLE: Project script.                                        |
# | PLIK: examples/lex_motion_curl.sh                          |
# | ROLA: cURL demo dla LEXENITH (Motion/CLDF/Why‑Not).          |
# +-------------------------------------------------------------+

set -euo pipefail

base="${BASE_URL:-http://127.0.0.1:8000}"

echo "# Motion"
curl -s -X POST "$base/v1/lexenith/motion/generate" -H 'Content-Type: application/json' \
  -d '{"case_id":"CER-LEX-001","pattern_id":"motion-dismiss","facts":{"a":1},"citations":["Art. 10","Art. 22"]}' | jq .

echo "# CLDF"
curl -s -X POST "$base/v1/lexenith/cldf/renormalize" -H 'Content-Type: application/json' \
  -d '{"citations":[{"text":"Art. 10","weight":1.0},{"text":"Art. 22","weight":2.0}],"damping":0.9}' | jq .

echo "# Why-Not"
curl -s -X POST "$base/v1/lexenith/why_not/export" -H 'Content-Type: application/json' \
  -d '{"claim":"x","counter_arguments":["y","z"]}' | jq .

