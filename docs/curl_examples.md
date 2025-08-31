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

- E2E publish via /v1/pco/bundle (status + ledger_ref in response JSON):
```
RID=case-002
SMT=$(printf '(set-logic ALL)\n(assert true)\n(check-sat)\n' | sha256sum | cut -d' ' -f1)
curl -s -X POST http://127.0.0.1:8000/v1/pco/bundle \
 -H 'Content-Type: application/json' \
 -d '{"rid":"'"$RID"'","smt2_hash":"'"$SMT"'","lfsc":"(lfsc proof)","merkle_proof":[]}' | jq .
```
