<!--
+======================================================================+
|                           CERTEUS — PR Template                      |
+======================================================================+
| ROLA / ROLE:                                                         |
|  PL: Lista kontrolna PR — najpierw README, potem kod.                |
|  EN: Pull Request checklist — README first, then code.               |
+======================================================================+
-->

## Cel / Purpose

<!-- Krótko: co i dlaczego. -->

## Zakres / Scope

<!-- Pliki/moduły, bez lania wody. -->

### Checklista jakości / Quality Checklist

- [ ] **Przeczytałem README.md (struktura, standard, CI).**
      I read the repository README (structure, coding standard, CI).
      `F:/projekty/certeus/README.md`
- [ ] Baner ASCII + PL/EN **docstring** w każdym nowym/zmienionym pliku.
- [ ] **Lint/format/testy** lokalnie zielone:
      `    uv run ruff check .; if ($LASTEXITCODE -eq 0) { uv run pytest -q }`
- [ ] **Nie zmieniałem portów** ani ścieżek serwowania (`/app`, `/static`).
- [ ] UI: zachowana paleta (biały/czarny/ciemnoszary/antracyt) i i18n PL/EN.
- [ ] Endpoints `/v1/ingest /v1/preview /v1/analyze /v1/export` **bez regresji**.
- [ ] Adaptery: jeśli dotyczy — **kontrakty** nietknięte, stuby/testy dodane.
- [ ] Windows: w razie problemów z linkami użyto `UV_LINK_MODE=copy`.
- [ ] Proof Gate/CI przechodzi (tests.yml, proof-gate.yml, ui-smoke).

### Dowody/artefakty / Evidence & Artifacts

<!-- Zrzuty ekranu UI, link do artefaktów CI, skrót logów testów. -->

### Ryzyko / Risk

<!-- Co może pójść nie tak i jak to mitigować. -->

### Notatki / Notes

<!-- Drobiazgi, które pomogą w review. -->
