<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/cookbooks/chatops_mailops.md                    |
| ROLE: Documentation page.                                    |
| PLIK: docs/cookbooks/chatops_mailops.md                    |
| ROLA: Dokumentacja.                                          |
+-------------------------------------------------------------+
-->

# ChatOps/MailOps — Cookbook (W1)

Krótki zestaw przykładów do szybkiego uruchomienia ChatOps/MailOps oraz weryfikacji Proof‑Only I/O.

## Wymagania

- Serwer dev: `python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`
- (opcjonalnie) Wymuszanie Proof‑Only I/O: `STRICT_PROOF_ONLY=1`

## ChatOps — przykłady

Proste, bezpieczne komendy (whitelist): `qtm.measure`, `cfe.geodesic`, `lexqft.tunnel`.

```bash
curl -s -H 'Content-Type: application/json' \
  -d '{"cmd":"cfe.geodesic","args":{}}' \
  http://127.0.0.1:8000/v1/chatops/command | jq .

curl -s -H 'Content-Type: application/json' \
  -d '{"cmd":"qtm.measure","args":{"operator":"W"}}' \
  http://127.0.0.1:8000/v1/chatops/command | jq .
```

Oczekiwane pola: `result.*` (np. `geodesic_action`, `verdict`, `p`).

## MailOps — ingest

Minimalny przykład z podstawowymi nagłówkami (SPF/DKIM/DMARC) i bez załączników:

```bash
curl -s -H 'Content-Type: application/json' \
  -d '{
        "mail_id":"MAIL-001",
        "from_addr":"alice@example.com",
        "to":["ops@example.com"],
        "subject":"Hello",
        "body_text":"Test",
        "spf":"pass","dkim":"pass","dmarc":"pass",
        "attachments":[]
      }' \
  http://127.0.0.1:8000/v1/mailops/ingest | jq .
```

Odpowiedź zawiera obiekt `io` zestandaryzowany do pól `io.email.*` oraz hash rejestrowany w Ledger (best‑effort).

## Proof‑Only I/O (opcjonalnie)

Wymuś dowodową publikowalność (publishable ⇒ PCO required) dla wybranych ścieżek, m.in. `/v1/mailops/ingest`:

```powershell
$env:STRICT_PROOF_ONLY = '1'
# brak tokenu ⇒ 403 DROP
curl -s -o /dev/null -w "%{http_code}\n" -H 'Content-Type: application/json' \
  -d '{"mail_id":"X","from_addr":"a@b","to":["c@d"],"attachments":[]}' \
  http://127.0.0.1:8000/v1/mailops/ingest
```

W trybie produkcyjnym dołącz JWS Ed25519 w nagłówku `Authorization: Bearer <token>` lub `X-PCO-Token: <token>`.

## Log sekwencji QTMP w Cockpicie

Strona `clients/web/public/quantum.html` posiada panel „Measurement Log” — przycisk „Refresh log” pobiera `GET /v1/qtm/history/{case}`. „Measure” aktualizuje log automatycznie.

