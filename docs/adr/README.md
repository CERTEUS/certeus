```
# +=============================================================+
# |                        CERTEUS — DOC                        |
# +=============================================================+
# | FILE: certeus/docs/adr/README.md                            |
# | TYPE: ADR Guidelines                                        |
# | FORGEHEADER: v2                                             |
# | UPDATED: 2025-09-08Z                                        |
# +=============================================================+
```

# ADR — Zasady i konwencje

- Nazewnictwo: `NNNN-title.md` (np. `0001-template.md`), numeracja rosnąco.
- Zawartość: Status, Kontekst, Decyzja, Konsekwencje, Linki (w tym role A0–A9 gdzie zasadne).
- Umiejscowienie: `certeus/docs/adr/`.
- Workflow:
  1) ADR `Proposed` → przegląd (A0 + właściciele domeny)
  2) Implementacja + ci‑gates zielone
  3) Status `Accepted` + link do PR i wdrożenia
  4) Deprecacja/następstwo przez nowy ADR (pole `Superseded by`)
- Spójność: zmiany w kontraktach (PCO/polityki/API) muszą odnotować wpływ na wersjonowanie (patrz: `policies/VERSIONING.md`).

Przykłady istniejących ADR: `ADR-0001-proof-only-io.md`, `ADR-0003-ci-gates.md`, `ADR-0004-redaction.md`, `ADR-0006-slo-gate.md`.

