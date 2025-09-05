# CERTEUS — Cockpit Ops Quickstart

Krótki przewodnik dla A6 (Cockpit/ChatOps/MailOps/Export) — jak szybko uruchomić i sprawdzić operacje w UI i z linii komend.

## Uruchomienie lokalnie

- API Gateway: `python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`
- Cockpit Index: `http://127.0.0.1:8000/app/public/index.html`

## ChatOps

- UI: `http://127.0.0.1:8000/app/public/chatops.html`
- API (curl):

```bash
curl -sS -X POST http://127.0.0.1:8000/v1/chatops/command \
  -H 'content-type: application/json' \
  -d '{"cmd":"qtm.measure","args":{"operator":"W","case":"chatops-case"}}' | jq
```

Oczekiwane: wynik pomiaru + nagłówki PCO (`X-CERTEUS-PCO-*`).

## MailOps

- UI: `http://127.0.0.1:8000/app/public/mailops.html`
- API (curl):

```bash
curl -sS -X POST http://127.0.0.1:8000/v1/mailops/ingest \
  -H 'content-type: application/json' \
  -d '{
    "mail_id":"mail-001",
    "thread_id":"thread-001",
    "from_addr":"alice@example.com",
    "to":["bob@example.com"],
    "subject":"Dowód i załączniki",
    "body_text":"W załączeniu przesyłam materiały.",
    "attachments":[{"filename":"plik.txt","content_type":"text/plain","size":10}]
  }' | jq
```

Tip: `PROOFS_FS_MATERIALIZE=1` materializuje stuby ProofFS do `data/proof_fs/...` (DEV/test).

## Export (pisma/raport)

- UI: `http://127.0.0.1:8000/app/public/export.html`
- API (curl):

```bash
curl -sS -X POST http://127.0.0.1:8000/v1/export \
  -H 'content-type: application/json' \
  -d '{"case_id":"lex-case-001","fmt":"report","analysis_result":{"type":"lex.letter.motion","title":"Wniosek","body":"…"},"write_ledger":false}' | jq
```

Wynik: ścieżka pliku w `exports/` oraz PCO w nagłówkach (`X-CERTEUS-PCO-export.*`).

## DevEx Playground

- UI: `http://127.0.0.1:8000/app/public/playground.html` — try‑now dla kluczowych endpointów, kopiowanie snippetów curl/SDK.

