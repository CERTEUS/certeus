# cURL Examples (MVP)

- Create ProofBundle:

```
curl -s -X POST http://127.0.0.1:8000/v1/pco/bundle \
 -H 'Content-Type: application/json' \
 -d '{"rid":"case-001","smt2_hash":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","lfsc":"(lfsc proof)","merkle_proof":[]}'
```

- Read Public PCO:

```
curl -s http://127.0.0.1:8000/pco/public/case-001
```

- JWKS:

```
curl -s http://127.0.0.1:8000/.well-known/jwks.json
```

- Metrics:

```
curl -s http://127.0.0.1:8000/metrics | head
```

- Cache Source:

```
curl -s -X POST http://127.0.0.1:8000/v1/sources/cache -H 'Content-Type: application/json' -d '{"uri":"https://isap.sejm.gov.pl/isap.nsf/DocDetails.xsp?id=WDU19970880553"}'
```

- ProofGate Publish Decision:

```
curl -s -X POST http://127.0.0.1:8000/v1/proofgate/publish -H 'Content-Type: application/json' -d '{"pco":{"case_id":"case-001","risk":{"ece":0.01,"brier":0.05,"abstain_rate":0.05}},"budget_tokens":10}'
```

- Ledger API (record/list/prove):

```
CASE=case-ledger-01
DOC_HASH="sha256:$(printf 'doc' | sha256sum | cut -d' ' -f1)"
curl -s -X POST http://127.0.0.1:8000/v1/ledger/record-input -H 'Content-Type: application/json' -d '{"case_id":"'"$CASE"'","document_hash":"'"$DOC_HASH"'"}'
curl -s http://127.0.0.1:8000/v1/ledger/$CASE/records | jq .
curl -s http://127.0.0.1:8000/v1/ledger/$CASE/prove | jq .
```

- Ledger Head (skrót sprawy):

```
CASE=case-ledger-01
curl -s http://127.0.0.1:8000/v1/ledger/$CASE | jq .
```

- E2E publish via /v1/pco/bundle (status + ledger_ref in response JSON):

```
RID=case-002
SMT=$(printf '(set-logic ALL)\n(assert true)\n(check-sat)\n' | sha256sum | cut -d' ' -f1)
curl -s -X POST http://127.0.0.1:8000/v1/pco/bundle \
 -H 'Content-Type: application/json' \
-d '{"rid":"'"$RID"'","smt2_hash":"'"$SMT"'","lfsc":"(lfsc proof)","merkle_proof":[]}' | jq .
```

## Marketplace (podpisy i instalacja)

- Lista wtyczek:

```
curl -s http://127.0.0.1:8000/v1/marketplace/plugins | jq .
```

- Weryfikacja podpisu manifestu (Ed25519, base64url):

```
# Załóż, że masz klucz publiczny w ENV: ED25519_PUBKEY_B64URL
MAN=plugins/demo_alpha/plugin.yaml
SIG=$(\.\.venv\\Scripts\\python.exe scripts\\marketplace\\sign_manifest.py --in "$MAN" --key .devkeys\\dev_ed25519.pem --print)
curl -s -X POST http://127.0.0.1:8000/v1/marketplace/verify_manifest \
  -H 'Content-Type: application/json' \
  -d '{"manifest_yaml":'"$(cat $MAN | sed -e 's/\\/\\\\/g' -e ':a;N;$!ba;s/\n/\\n/g')"',"signature_b64u":"'"$SIG"'"}'
```

- Instalacja/upgrade wtyczki (po weryfikacji podpisu):

```
NAME=demo_alpha
MAN=plugins/demo_alpha/plugin.yaml
SIG=$(\.\.venv\\Scripts\\python.exe scripts\\marketplace\\sign_manifest.py --in "$MAN" --key .devkeys\\dev_ed25519.pem --print)
curl -s -X POST http://127.0.0.1:8000/v1/marketplace/install \
  -H 'Content-Type: application/json' \
  -d '{"name":"'"$NAME"'","manifest_yaml":'"$(cat $MAN | sed -e 's/\\/\\\\/g' -e ':a;N;$!ba;s/\n/\\n/g')"',"signature_b64u":"'"$SIG"'"}' | jq .
```

## Billing / Cost‑tokens

- Ustaw quota:

```
curl -s -X POST http://127.0.0.1:8000/v1/billing/quota \
  -H 'Content-Type: application/json' \
  -d '{"tenant":"acme","units":100}' | jq .
```

- Odczyt salda (dla tenant `acme`):

```
curl -s http://127.0.0.1:8000/v1/billing/balance -H 'X-Tenant-ID: acme' | jq .
```

- Allocate (np. doładowanie, PENDING→allocate):

```
curl -s -X POST http://127.0.0.1:8000/v1/billing/allocate \
  -H 'X-Tenant-ID: acme' -H 'Content-Type: application/json' \
  -d '{"units":25}' | jq .
```

- Refund (np. korekta +5):

```
curl -s -X POST http://127.0.0.1:8000/v1/billing/refund \
  -H 'Content-Type: application/json' \
  -d '{"tenant":"acme","units":5}' | jq .

- Polityki i tier:

```
curl -s http://127.0.0.1:8000/v1/billing/policies | jq .

curl -s http://127.0.0.1:8000/v1/billing/tenant_tier -H 'X-Tenant-ID: acme' | jq .
```

- Estymator kosztu akcji:

```
curl -s -X POST http://127.0.0.1:8000/v1/billing/estimate \
  -H 'X-Tenant-ID: acme' -H 'Content-Type: application/json' \
  -d '{"action":"qtm.measure"}' | jq .
```
```

## FINENITH — Q‑Alpha (W16)

- Symulacja strategii (per‑tenant przez `X-Tenant-ID`):

```
curl -s -X POST http://127.0.0.1:8000/v1/fin/alpha/simulate \
  -H 'X-Tenant-ID: acme' -H 'Content-Type: application/json' \
  -d '{"strategy_id":"qalpha-momentum","capital":100000,"horizon_days":30}' | jq .
```

- Odczyt ostatnich PnL:

```
curl -s http://127.0.0.1:8000/v1/fin/alpha/pnl -H 'X-Tenant-ID: acme' | jq .
```

## LEXENITH — Pilot (W16)

- Lista spraw pilotażowych:

```
curl -s http://127.0.0.1:8000/v1/lexenith/pilot/cases | jq .
```

- Przekazanie feedbacku (ocena 1–5):

```
curl -s -X POST http://127.0.0.1:8000/v1/lexenith/pilot/feedback \
  -H 'X-Tenant-ID: acme' -H 'Content-Type: application/json' \
  -d '{"case_id":"LEX-PILOT-001","rating":5,"comments":"Szybki wynik i dobre cytaty."}' | jq .
```

## SLO per‑tenant (W16)

- Panel p95 per‑tenant (Grafana expr):

```
histogram_quantile(0.95, sum(rate(certeus_http_request_duration_ms_tenant_bucket[5m])) by (le, tenant))
```

- Error‑rate per‑tenant (5m, Grafana expr):

```
sum(rate(certeus_http_requests_total{status=~"5.."}[5m])) by (tenant)
/ sum(rate(certeus_http_requests_total[5m])) by (tenant)
```
