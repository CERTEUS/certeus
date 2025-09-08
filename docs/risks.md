```
# +=============================================================+
# |                        CERTEUS — DOC                        |
# +=============================================================+
# | FILE: certeus/docs/risks.md                                 |
# | TYPE: Top‑10 Risks & Mitigations                            |
# | FORGEHEADER: v2                                             |
# | UPDATED: 2025-09-08Z                                        |
# +=============================================================+
```

# Ryzyka top‑10 i mitigacje

1. Regress p95/p99 (SLO) — Mitigacja: SLO‑gate + smoke + rollback.
2. Rozjazd kontraktów (PCO/polityki/API) — Mitigacja: VERSIONING + tests/contract.
3. Luki supply‑chain — Mitigacja: SBOM/provenance (report‑only w Fazie I).
4. Niespójność ról/praw — Mitigacja: Governance Pack + OPA roles; testy gate.
5. Błędy schema PCO — Mitigacja: walidacja jsonschema + testy E2E.
6. Brak deterministyczności — Mitigacja: seeds, fixed TZ, PYTHONHASHSEED.
7. Regres a11y/i18n — Mitigacja: smoke + checklisty UI.
8. Integracja ledger/anchor — Mitigacja: testy CLI + manifest anchor.
9. Zgubione artefakty — Mitigacja: upload SBOM/provenance/boundary do CI.
10. Dług dokumentacji — Mitigacja: ADR workflow + G1‑pre checklist.

