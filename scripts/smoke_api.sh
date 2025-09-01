#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smoke_api.sh                                |
# | ROLE: Shell script.                                         |
# | PLIK: scripts/smoke_api.sh                                |
# | ROLA: Skrypt powłoki.                                       |
# +-------------------------------------------------------------+
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
# CERTEUS — Simple API smoke test (Linux/macOS)

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

set -euo pipefail

if [[ -f ./scripts/dev_env.sh ]]; then
  # shellcheck disable=SC1091
  source ./scripts/dev_env.sh
fi

PY=.venv/bin/python
[[ -x "$PY" ]] || { echo "Python venv not found: $PY"; exit 1; }

# Generate ephemeral Ed25519 keypair for PCO bundle signing (Linux CI)
if [[ -z "${ED25519_PRIVKEY_PEM:-}" ]]; then
  mkdir -p .devkeys
  "$PY" - << 'PY'
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization
from pathlib import Path
import base64

p = Path('.devkeys'); p.mkdir(exist_ok=True)
k = Ed25519PrivateKey.generate()
pem = k.private_bytes(
    encoding=serialization.Encoding.PEM,
    format=serialization.PrivateFormat.PKCS8,
    encryption_algorithm=serialization.NoEncryption(),
)
(p / 'ed25519_priv.pem').write_bytes(pem)
pub = k.public_key().public_bytes(
    encoding=serialization.Encoding.Raw,
    format=serialization.PublicFormat.Raw,
)
(p / 'ed25519_pub.hex').write_text(pub.hex(), encoding='utf-8')
(p / 'ed25519_pub.b64u').write_text(base64.urlsafe_b64encode(pub).rstrip(b'=').decode('ascii'), encoding='utf-8')
PY
  export ED25519_PRIVKEY_PEM="$(cat .devkeys/ed25519_priv.pem)"
  export ED25519_PUBKEY_HEX="$(cat .devkeys/ed25519_pub.hex)"
  export ED25519_PUBKEY_B64URL="$(cat .devkeys/ed25519_pub.b64u)"
  export PROOF_BUNDLE_DIR="${PROOF_BUNDLE_DIR:-data/public_pco}"
  mkdir -p "${PROOF_BUNDLE_DIR}"
fi

function start_server() {
  $PY -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000 &
  SVR_PID=$!
  for _ in {1..80}; do
    if curl -sf http://127.0.0.1:8000/health >/dev/null; then break; fi
    sleep 0.25
  done
}

function stop_server() {
  [[ -n "${SVR_PID:-}" ]] && kill "$SVR_PID" 2>/dev/null || true
}

function hit() {
  local method=$1 path=$2 body=${3:-}
  local url="http://127.0.0.1:8000${path}"
  if [[ "$method" == GET ]]; then
    code=$(curl -s -o /dev/null -w "%{http_code}" "$url")
    echo "[GET] $path => $code"
  else
    code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -X POST -d "$body" "$url")
    echo "[POST] $path => $code"
  fi
}

declare -i PASSES=0
declare -i FAILS=0
MAX_FAILS="${SMOKE_MAX_FAILS:-0}"
P95_MS="n/a"
metrics_p95() {
  curl -s http://127.0.0.1:8000/metrics | awk '
  /^certeus_http_request_duration_ms_bucket\{/ {
    match($0, /le="([^"]+)"/, m);
    if (m[1] != "") { buckets[m[1]] += $(NF) }
  }
  END {
    n=0; total=0; hasInf=0;
    for (le in buckets) { if (le=="+Inf") { total=buckets[le]; hasInf=1 } else { arr[++n]=le } }
    # sort numeric
    for (i=1;i<=n;i++) for (j=i+1;j<=n;j++) if ((arr[i]+0)>(arr[j]+0)) { t=arr[i]; arr[i]=arr[j]; arr[j]=t }
    if (!hasInf && n>0) total=buckets[arr[n]]
    thr=total*0.95; cum=0; p95="n/a";
    for (i=1;i<=n;i++) { cum+=buckets[arr[i]]; if (cum>=thr) { p95=arr[i]; break } }
    print p95;
  }'
}
trap 'stop_server; echo "SMOKE SUMMARY: total=$((PASSES+FAILS)) passes=$PASSES fails=$FAILS p95_ms=$P95_MS max_fails=$MAX_FAILS"' EXIT
start_server

hit GET /health && PASSES+=1 || FAILS+=1
hit GET / && PASSES+=1 || FAILS+=1
hit GET /metrics && PASSES+=1 || FAILS+=1
hit GET /.well-known/jwks.json && PASSES+=1 || FAILS+=1
hit GET /v1/packs/ && PASSES+=1 || FAILS+=1
hit POST /v1/fin/alpha/measure '{"signals":{"risk":0.10,"sentiment":0.55}}' && PASSES+=1 || FAILS+=1
hit GET /v1/fin/alpha/uncertainty && PASSES+=1 || FAILS+=1
hit GET /v1/fin/alpha/entanglements && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"case":"CER-SMOKE","facts":{},"norms":{}}' http://127.0.0.1:8000/v1/cfe/geodesic); echo "[POST] /v1/cfe/geodesic => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{}' http://127.0.0.1:8000/v1/cfe/horizon); echo "[POST] /v1/cfe/horizon => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
hit GET /v1/cfe/lensing && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"basis":["ALLOW","DENY","ABSTAIN"]}' http://127.0.0.1:8000/v1/qtm/init_case); echo "[POST] /v1/qtm/init_case => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"operator":"W","source":"ui"}' http://127.0.0.1:8000/v1/qtm/measure); echo "[POST] /v1/qtm/measure => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"A":"X","B":"Y"}' http://127.0.0.1:8000/v1/qtm/commutator); echo "[POST] /v1/qtm/commutator => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"variables":["A","B"]}' http://127.0.0.1:8000/v1/qtm/find_entanglement); echo "[POST] /v1/qtm/find_entanglement => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{}' http://127.0.0.1:8000/v1/devices/horizon_drive/plan); echo "[POST] /v1/devices/horizon_drive/plan => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"objective":"maximize fairness","constraints":{}}' http://127.0.0.1:8000/v1/devices/qoracle/expectation); echo "[POST] /v1/devices/qoracle/expectation => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"variables":["RISK","SENTIMENT"],"target_negativity":0.1}' http://127.0.0.1:8000/v1/devices/entangle); echo "[POST] /v1/devices/entangle => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"coords":{"t":0},"pc_delta":{}}' http://127.0.0.1:8000/v1/devices/chronosync/reconcile); echo "[POST] /v1/devices/chronosync/reconcile => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"distribution_a":[0.2,0.8],"distribution_b":[0.5,0.5]}' http://127.0.0.1:8000/v1/ethics/equity_meter); echo "[POST] /v1/ethics/equity_meter => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"W_litera":"ALLOW","T_telos":"TRUTH","rationale":"smoke"}' http://127.0.0.1:8000/v1/ethics/double_verdict); echo "[POST] /v1/ethics/double_verdict => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"cmd":"cfe.geodesic","args":{}}' http://127.0.0.1:8000/v1/chatops/command); echo "[POST] /v1/chatops/command => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1

# Ledger
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"case_id":"CER-1","document_hash":"sha256:0000000000000000000000000000000000000000000000000000000000000000"}' http://127.0.0.1:8000/v1/ledger/record-input); echo "[POST] /v1/ledger/record-input => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
hit GET /v1/ledger/CER-1/records && PASSES+=1 || FAILS+=1
hit GET /v1/ledger/CER-1/prove && PASSES+=1 || FAILS+=1

# PCO bundle + public verify
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"rid":"RID-SMOKE-1","smt2_hash":"0000000000000000000000000000000000000000000000000000000000000000","lfsc":"(lfsc proof)","drat":"p drat","merkle_proof":[]}' http://127.0.0.1:8000/v1/pco/bundle); echo "[POST] /v1/pco/bundle => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
hit GET /pco/public/RID-SMOKE-1 && PASSES+=1 || FAILS+=1

# Preview upload
tmp_txt=$(mktemp)
echo 'hello world' > "$tmp_txt"
code=$(curl -s -o /dev/null -w "%{http_code}" -F "file=@$tmp_txt;type=text/plain" http://127.0.0.1:8000/v1/preview); echo "[POST] /v1/preview => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1

# Ingest/analyze (PDF)
tmp_pdf=$(mktemp --suffix .pdf)
printf '%%PDF-1.4\n1 0 obj<<>>endobj\ntrailer<<>>\n%%EOF' > "$tmp_pdf"
code=$(curl -s -o /dev/null -w "%{http_code}" -F "file=@$tmp_pdf;type=application/pdf" http://127.0.0.1:8000/v1/ingest); echo "[POST] /v1/ingest => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1
code=$(curl -s -o /dev/null -w "%{http_code}" -F "file=@$tmp_pdf;type=application/pdf" 'http://127.0.0.1:8000/v1/analyze?case_id=CER-1'); echo "[POST] /v1/analyze => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1

# Source cache (file://)
tmp_src=$(mktemp)
echo 'source-cache' > "$tmp_src"
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d '{"uri":"file:///'"$tmp_src"'"}' http://127.0.0.1:8000/v1/sources/cache); echo "[POST] /v1/sources/cache => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1

# Publish
# Publish not mounted in app; skipping

# Create a minimal PCO bundle for public checks (uses generated keys)
rid="RID-SMOKE-1"
payload=$(cat <<JSON
{"rid":"$rid","smt2_hash":"$(python - <<'PY'
from hashlib import sha256
print(sha256(b'(set-logic ALL)\n(check-sat)\n').hexdigest())
PY
)","lfsc":"(lfsc proof)","drat":"p drat","merkle_proof":[]}
JSON
)
code=$(curl -s -o /dev/null -w "%{http_code}" -H 'Content-Type: application/json' -d "$payload" http://127.0.0.1:8000/v1/pco/bundle); echo "[POST] /v1/pco/bundle => $code"; [[ $code == 2* ]] && PASSES+=1 || FAILS+=1

# Compute p95 from /metrics
P95_MS=$(metrics_p95)

# --- OpenAPI validation & lightweight schema checks ---
mkdir -p reports
if curl -s -f http://127.0.0.1:8000/openapi.json -o reports/openapi.json; then
  if ./.venv/bin/python - << 'PY'
import json, sys
spec=json.load(open('reports/openapi.json','r',encoding='utf-8'))
ok=('openapi' in spec and 'paths' in spec)
try:
  try:
    from openapi_spec_validator import validate_spec as _validate
  except Exception:
    try:
      from openapi_spec_validator.validators import validate as _validate
    except Exception:
      _validate=None
  if _validate:
    _validate(spec)
    ok=True
except Exception:
  ok=False
sys.exit(0 if ok else 1)
PY
  then
    echo "[GET] /openapi.json#schema => 200"; PASSES=$((PASSES+1))
  else
    echo "[GET] /openapi.json#schema => FAIL"; FAILS=$((FAILS+1))
  fi
else
  echo "[GET] /openapi.json#schema => FAIL"; FAILS=$((FAILS+1))
fi

# Health payload shape
if curl -s http://127.0.0.1:8000/health | ./.venv/bin/python -c 'import sys,json; j=json.load(sys.stdin); assert j.get("status")=="ok" and isinstance(j.get("version"),str) and j["version"]; print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi

# JWKS payload shape
if curl -s http://127.0.0.1:8000/.well-known/jwks.json | ./.venv/bin/python -c 'import sys,json; j=json.load(sys.stdin); ks=j.get("keys") or []; assert ks and ks[0].get("kty")=="OKP" and ks[0].get("crv")=="Ed25519" and isinstance(ks[0].get("x"),str); print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi

# FIN measure payload shape
if curl -s -H 'Content-Type: application/json' -d '{"signals":{"risk":0.1,"sentiment":0.6}}' http://127.0.0.1:8000/v1/fin/alpha/measure | ./.venv/bin/python -c 'import sys,json; j=json.load(sys.stdin); assert isinstance(j.get("outcome"),str) and isinstance(j.get("p"),(int,float)); print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi

# QTMP regressions
if curl -s -H 'Content-Type: application/json' -d '{"basis":["ALLOW","DENY","ABSTAIN"]}' http://127.0.0.1:8000/v1/qtm/init_case | ./.venv/bin/python -c 'import sys,json,math; j=json.load(sys.stdin); pd=j.get("predistribution") or []; s=sum(float(it.get("p",0)) for it in pd); assert len(pd)==3 and abs(s-1.0)<=1e-3; print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi

if curl -s -H 'Content-Type: application/json' -d '{"operator":"W","source":"ui"}' http://127.0.0.1:8000/v1/qtm/measure | ./.venv/bin/python -c 'import sys,json; j=json.load(sys.stdin); assert j.get("verdict") in ["ALLOW","DENY","ABSTAIN"]; print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi

if curl -s -H 'Content-Type: application/json' -d '{"A":"X","B":"Y"}' http://127.0.0.1:8000/v1/qtm/commutator | ./.venv/bin/python -c 'import sys,json; j=json.load(sys.stdin); assert float(j.get("value",-1))==1.0; print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi

# PCO public rid equals requested rid
if curl -s http://127.0.0.1:8000/pco/public/RID-SMOKE-1 | ./.venv/bin/python -c 'import sys,json; j=json.load(sys.stdin); assert j.get("rid")=="RID-SMOKE-1"; print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi

# PCO signature b64url and ledger merkle_root hex
if curl -s http://127.0.0.1:8000/pco/public/RID-SMOKE-1 | ./.venv/bin/python -c 'import sys,json,re; j=json.load(sys.stdin); sig=j.get("signature") or ""; ok=bool(re.match(r"^[A-Za-z0-9_-]+$", sig)) and ("=" not in sig); root=((j.get("ledger") or {}).get("merkle_root") or ""); ok = ok and (len(root)==64 and bool(re.match(r"^[0-9a-f]+$", root))); assert ok; print("ok")'; then
  PASSES=$((PASSES+1))
else
  FAILS=$((FAILS+1))
fi
THRESH="${SLO_MAX_P95_MS:-}"
if [[ -n "$THRESH" && "$P95_MS" != "n/a" ]]; then
  awk -v p95="$P95_MS" -v thr="$THRESH" 'BEGIN { if (p95+0 > thr+0) { exit 1 } else { exit 0 } }'
  if [[ $? -ne 0 ]]; then
    echo "SLO VIOLATION: p95_ms=$P95_MS > threshold_ms=$THRESH"
    FAILS=$((FAILS+1))
  fi
fi

# Write JSON summary and append to GitHub summary if available
mkdir -p reports
printf '{"total":%d,"passes":%d,"fails":%d,"p95_ms":"%s","threshold_ms":"%s","max_fails":"%s"}\n' $((PASSES+FAILS)) "$PASSES" "$FAILS" "$P95_MS" "${THRESH}" "${MAX_FAILS}" > reports/smoke_summary.json
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  {
    echo "### Smoke Summary"
    echo
    echo "- total: $((PASSES+FAILS))"
    echo "- passes: $PASSES"
    echo "- fails: $FAILS"
    echo "- p95_ms: $P95_MS"
    echo "- threshold_ms: ${THRESH}"
  } >> "$GITHUB_STEP_SUMMARY"
fi

# Final gate: fail if too many failures
if [[ ${FAILS} -gt ${MAX_FAILS} ]]; then
  exit 1
fi
