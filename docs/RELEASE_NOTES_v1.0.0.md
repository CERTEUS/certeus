# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/RELEASE_NOTES_v1.0.0.md                        |
# | ROLE: Project Markdown.                                     |
# | PLIK: docs/RELEASE_NOTES_v1.0.0.md                        |
# | ROLA: Dokument wydania v1.0.0.                               |
# +-------------------------------------------------------------+

## CERTEUS v1.0.0 — Launch (W18)

- Data: 2025-09-03
- Commit: HEAD (work/daily → main po zielonych bramkach)
- Stan bramek: zielone (Smoke ubuntu/windows, ci-gates)

### Najważniejsze
- API Gateway: zgodność runtime OpenAPI z kontraktem w `docs/api/openapi.yaml`.
- ProofGate: ścieżka `/v1/proofgate/publish` dostępna w gateway (alias do kontraktu).
- PCO public: alias `/pco/public/{case_id}` obok `/pco/public/{rid}`.
- Ledger: `GET /v1/ledger/{case_id}` (head + długość łańcucha).
- FINENITH: `fin.alpha` (measure/simulate/pnl, komutator R/S).
- LEXENITH: Motion generator, CLDF renormalize, Why‑Not export.
- Observability: metryki p95, licznik żądań, metryki FIN.
- Proof‑Only I/O: middleware aktywne (bezpieczny no‑op bez wymuszania).

### Stabilność i testy
- Lint: ruff clean.
- Testy: 124 passed, 1 skipped (CLI uv smoke na Windows pomijany) — raport w `reports/junit.xml`.
- Hypothesis: profil CI z `suppress_health_check=too_slow` (tylko dla testów właściwości).

### Co nowego w dokumentacji i przykładach
- Cookbooks:
  - `docs/cookbooks/fin_alpha.md` — szybki start Q‑Alpha.
  - `docs/cookbooks/lex_micro_court.md` — Micro‑Court i CLDF.
- Przykłady:
  - `examples/fin_alpha_curl.sh`, `examples/lex_motion_curl.sh`.
- Uzupełnienia `docs/curl_examples.md` o ProofGate/PCO/Ledger.

### Znane ograniczenia
- ProofGate w gateway to alias kontraktowy (pełna logika w `services/proofgate/app.py`).
- Profile canary/progressive kontrolowane w CI/infra (poza zakresem repo kodu aplikacji).

### Następne kroki (1.1)
- Devices+: rozbudowa Q‑Oracle/Entangler, SYNAPSY P2P.
- Packs: rozszerzenia FIN/LEX/SEC.
- Med/Sec packs i SLO per tenant w środowisku klientów.

