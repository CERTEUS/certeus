# W16 — Changelog (Piloty zewnętrzne)

- FIN (Q‑Alpha): dodano `/v1/fin/alpha/simulate` i `/v1/fin/alpha/pnl` (PCO w nagłówkach; per‑tenant przez `X-Tenant-ID`).
- LEX (pilot): dodano `/v1/lexenith/pilot/cases` oraz `/v1/lexenith/pilot/feedback` (metryki feedbacku + PCO w nagłówku).
- Observability: metryki SLO per‑tenant (`certeus_http_request_duration_ms_tenant`, `certeus_http_requests_total`) + dwa panele na dashboardzie Grafana.
- Middleware metryk: uproszczony do pojedynczej instancji (usunięto duplikat), rejestruje tenant/path/method/status.
- curl examples: uzupełniono przykłady dla W16 (pilot/fin/SLO per‑tenant).
- Demo ruchu per‑tenant: `scripts/demos/w16_generate_tenant_traffic.py` (zmienne: `CERTEUS_BASE`, `N_REQ`, `SLEEP_S`).

Top‑10 pain points (skrót; do rozwinięcia po feedbacku pilotów):
- Brak per‑tenant SLO → dodano metryki i panele.
- Brak widoku PnL → dodano endpoint `/v1/fin/alpha/pnl` (ostatnie uruchomienia).
- Potrzeba prostego kanału feedback → `/v1/lexenith/pilot/feedback` z oceną 1–5 i metrykami.
- Spójność ścieżek OpenAPI → wszystkie nowe endpointy pod `/v1/*` z tagami domenowymi.
- CORS dev: włączony wildcard; w produkcji należy zawęzić (`ALLOW_ORIGINS`).

Uwaga: pełna analiza UX po zakończeniu tygodnia; plik będzie aktualizowany.
