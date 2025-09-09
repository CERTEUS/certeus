## PR Checklist

- [ ] Lint/format: `ruff check . --fix` i `ruff format .` — lokalnie zielone
- [ ] Testy lokalnie zielone: `pytest -q`
- [ ] Dokumentacja zaktualizowana (README/WORKLOG/CHANGELOG/RELEASE_NOTES)
- [ ] OpenAPI w sync (jeśli dotyczy API): `tools/openapi-sync.sh verify`
- [ ] Sekrety/usługi zewnętrzne niewyeksponowane (skany nie wykazują problemów)
- [ ] Polityka gałęzi: PR kierowany na `main`; `work/daily` tylko do pracy dziennej
- [ ] CI: „Tests” zielone; bramki `ci-gates` akceptowalne (jeśli uruchamiane)

Opis zmian:

- …

