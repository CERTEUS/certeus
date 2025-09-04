<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/w1_demo.md                             |
| ROLE: Runbook (W1 Demo).                                     |
| PLIK: docs/runbooks/w1_demo.md                             |
| ROLA: Runbook (Demo tygodnia 1).                             |
+-------------------------------------------------------------+
-->

# W1 — Demo (10 minut)

Cel: pokazać koniec‑do‑końca przepływ Cockpit/ChatOps/MailOps → Telemetria → Ledger (Proof‑Native), zgodnie z planem W1.

## 1) Uruchom API

```
python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
```

Sprawdź: `curl -s http://127.0.0.1:8000/health`

## 2) ChatOps: geodesic

```
curl -s -H 'Content-Type: application/json' \
  -d '{"cmd":"cfe.geodesic","args":{}}' \
  http://127.0.0.1:8000/v1/chatops/command | jq .
```

Oczekuj pola `geodesic_action`.

## 3) MailOps: ingest

```
curl -s -H 'Content-Type: application/json' \
  -d '{"mail_id":"DEMO-W1-EMAIL","from_addr":"demo@example.com","to":["ops@example.com"],"subject":"Demo","body_text":"W1 demo","spf":"pass","dkim":"pass","dmarc":"pass","attachments":[]}' \
  http://127.0.0.1:8000/v1/mailops/ingest | jq .
```

Odpowiedź zawiera zestandaryzowane pola `io.email.*` i (best‑effort) wpis do Ledger.

## 4) QTMP: pomiar i log sekwencji

```
curl -s -H 'Content-Type: application/json' \
  -d '{"operator":"L","source":"demo","case":"DEMO-W1"}' \
  http://127.0.0.1:8000/v1/qtm/measure | jq .

curl -s http://127.0.0.1:8000/v1/qtm/history/DEMO-W1 | jq .
```

Sprawdź w przeglądarce panel „Measurement Log” na `http://127.0.0.1:8000/app/public/quantum.html` (pole case: `DEMO-W1`).

## 5) Telemetria CFE/lexqft

```
curl -s http://127.0.0.1:8000/v1/cfe/curvature | jq .
curl -s http://127.0.0.1:8000/v1/lexqft/coverage | jq .
```

## 6) Ledger (wpisy)

```
curl -s http://127.0.0.1:8000/v1/ledger/DEMO-W1/records | jq .
```

## 7) Skrypt demo (automatycznie)

- PowerShell: `pwsh -File scripts/demos/w1_demo.ps1`
- Bash: `bash scripts/demos/w1_demo.sh`

Wynik: `reports/w1_demo.json` (agregat odpowiedzi demo).

## 8) Proof‑Only I/O (opcjonalnie)

```
export STRICT_PROOF_ONLY=1   # PS: $env:STRICT_PROOF_ONLY='1'
# próba bez tokenu → 403
curl -s -o /dev/null -w "%{http_code}\n" -H 'Content-Type: application/json' \
  -d '{"mail_id":"X","from_addr":"a@b","to":["ops@example.com"],"attachments":[]}' \
  http://127.0.0.1:8000/v1/mailops/ingest
```

## KPI (W1)

- Cockpit: heatmapy + log sekwencji widoczne.
- ChatOps/MailOps: proste wywołania przechodzą (2xx) w DEV.
- Telemetria: `/v1/cfe/curvature.kappa_max`, `/v1/lexqft/coverage.coverage_gamma` dostępne.
- Cały E2E ≤ 10 min (manualny) lub ≤ 3 min (skrypt). 

