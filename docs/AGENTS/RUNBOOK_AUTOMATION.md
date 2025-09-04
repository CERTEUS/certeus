# CERTEUS — Runbook Automatyzacji (dla agentów)

Cel: Utrzymać czysty core (prywatny) i publiczny mirror LITE z zielonymi checkami, minimalizując koszty CI.

## Codzienny SOP
- Lint/test: `python -m ruff check . --fix && python -m ruff format . && pytest -q`
- Push roboczy: `python scripts/git_push.py --to work/daily`
- Core CI na gałęzi roboczej: ciężkie workflowy ograniczone (ci-gates/UI/Docs/denylist uruchamiają się tylko na main lub w PR)
- Mirror: publikacja przez `Publish-Public-Mirror` (po Promote-Daily-to-Main, oraz na push: main)

## Tygodniowy promote
- Upewnij się, że tydzień zamknięty i testy zielone.
- Zrób commit z markerem tygodnia `[week-end]` lub trailer `weekly-promote: true`.
- Promote do `main` (workflow `promote-daily-to-main.yml`), po zielonych bramkach.
- Po merge na `main` w core: mirror publikuje się automatycznie (allowlista LITE, squash commit).

## Publiczny mirror (CERTEUS/certeus-public)
- Wymagane checki (branch protection): `CI-Public-Light`, `Policy-Scan`.
- Auto-merge: włączony, delete branch on merge: włączony.
- Force‑push: wyłączony.
- README i MkDocs w mirrorze są minimalne (bez „sitemap”); publikowane tylko ścieżki z `tools/automation/public_allowlist.txt`.

## Komendy kontroli (GH CLI)
- Core runs (ostatnie): `gh run list -L 10`
- Public runs: `gh run list -R CERTEUS/certeus-public -L 10`
- Ochrona gałęzi (mirror): `gh api repos/CERTEUS/certeus-public/branches/main/protection`
- Gałęzie (mirror): `gh api repos/CERTEUS/certeus-public/branches?per_page=100`

## Najczęstsze problemy i rozwiązania
- „Job was not started (billing/spending limit)”: ograniczyliśmy workflowy core do `main` lub PR; na `work/daily` nie biegają ciężkie joby.
- Brak pluginu MkDocs `sitemap`: usunięty z publicznych configów; CI nie próbuje go instalować.
- Sekrety/tokeny: nie trzymamy w repo; `gh auth` lub `.devkeys/*.txt` (lokalnie, ignorowane).

## 90 dni — dokumenty
- Final: `docs/reports/90dni_final_status.md`
- Coverage: `docs/reports/90dni_coverage_report.md`
- Status matrix: `docs/reports/90dni_status_matrix.md`
- Archiwum planu: `docs/90_dni_work.md` (nie modyfikować; służy jako historyczny opis zakresów).

## Konwencje
- Commit: Conventional Commits (feat/fix/chore/docs/ci/perf).
- PR: auto-merge po zielonych checkach.
- Mirror: squash z allowlisty; publikacja na `main`.

