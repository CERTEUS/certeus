```
# +=============================================================+
# |                        CERTEUS — DOC                        |
# +=============================================================+
# | FILE: certeus/docs/roadmap.md                               |
# | TYPE: Phase I Roadmap & Milestones (T1–T6)                   |
# | FORGEHEADER: v2                                             |
# | UPDATED: 2025-09-08Z                                        |
# +=============================================================+
```

# Faza I — Roadmapa (T1–T6)

Krótki plan prac i kamieni milowych wymaganych do domknięcia Fazy I. Zgodnie z rolami A0–A9 oraz bramką G1.

## Role A0–A9 (linki)
- A0 — PM/Architekt: ../../tasks/A0.md
- A1 — PCO & Verifier: ../../tasks/A1.md
- A2 — Formal Methods: ../../tasks/A2.md
- A3 — Provenance/Ledger: ../../tasks/A3.md
- A4 — SLO/Observability: ../../tasks/A4.md
- A5 — Security/Supply Chain: ../../tasks/A5.md
- A6 — API/Gateway/Policies: ../../tasks/A6.md
- A7 — Cockpit/UI: ../../tasks/A7.md
- A8 — Bench/Research: ../../tasks/A8.md
- A9 — QA/Test & Release: ../../tasks/A9.md

## Cel Fazy I
- PCO v0.3 przyjęte w całym przepływie (SDK/ProofGate/Tests).
- Proof‑Only: publikacja przez ProofGate z walidacją PCO i polityk (report‑only tam, gdzie wymagane).
- SLO/Perf: progi i smoki, brak regresji krytycznych; raport p95.
- Governance: pakiet ról/akcji i spójność z OPA; RACI opublikowane.
- Compliance/Supply‑chain: SBOM + provenance w CI (artefakty) oraz podstawowe bramki polityk (report‑only).
- Dokumenty governance (ADR/README), ryzyka, wersjonowanie — gotowe.

## Kamienie milowe i orientacyjna oś czasu
- W14: PCO v0.3, ProofGate publish ścieżka MVP, smoki SLO/Perf (report‑only), Marketplace/Pack ABI Gate (report‑only).
- W15: Governance Pack + roles policy w ProofGate, OpenAPI contract smoke, i18n/A11y baseline.
- W16: Supply‑chain (SBOM/provenance) w ci‑gates, Boundary snapshot/diff artefakt.
- W17: Path‑Coverage feed (FIN→lexqft), Gauge drift smoke, polityka risk thresholds w DEMO.
- W18: G1‑pre i poprawki; audyt G1 i raport PASS/FAIL.

## Zakres prac (epiki)
- ProofGate i PCO: decyzje `PUBLISH/CONDITIONAL/PENDING/ABSTAIN`, walidacja SEC‑PCO (VALIDATE_PCO=1 report‑only).
- SLO‑Gate: definicja progów (ECE, Brier, abstain_rate, p95) + smoki raportujące.
- Governance: OPA (roles) + Governance Pack; egzekucja union ról publikacji.
- Supply‑chain: generacja i weryfikacja SBOM/provenance; przygotowanie do enforce.
- UI/Cockpit: minimalny PCO viewer i checklisty policy.
- OpenAPI/i18n/A11y: walidacja kontraktu, semantyka i dostępność baseline.

## Kryteria wyjścia (Exit, do G1)
- ci‑gates zielone (style/lint/tests/smokes/gates; wymagane: Smoke ubuntu/windows + ci‑gates).
- Dokumenty: roadmapa, RACI, risks, VERSIONING, ADR template/README, G1_pre_review, G1_report.
- PCO v0.3 w testach E2E; SEC‑PCO schema weryfikowana (report‑only).
- Governance spójne (OPA roles + Governance Pack) i sprawdzone w ci‑gates.
- Artefakty: SBOM + provenance zebrane; raporty perf/SLO.

## Zależności i ryzyka
- Patrz: docs/risks.md oraz manifest (sekcje SLO‑Gate, Proof‑Only, Compliance).

## RACI
- Patrz: docs/raci.md (Faza I — odpowiedzialności A0–A9).

