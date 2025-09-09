# Developer Workflow (Public tests vs Private build)

UWAGA - Zasada niezmienna (Immutable Rule)

- Publikujemy wyłącznie to, co jest jawnie dozwolone przez allowlistę LITE (mirror publiczny). Wszystko inne zostaje w repo prywatnym i przechodzi przez bramki (gitleaks/policy-scan/branch-protection) - bez wyjątków.
- Pełen opis: zob. `docs/AGENTS/README.md` (sekcja: Zasada niezmienna/Immutable Rule).

Checklist (release/publish)

- [ ] Ustaw/zweryfikuj Social preview (og.png) w `CERTEUS/certeus-public` (Settings → General → Social preview).

1) Pracuj lokalnie na gałęzi `work/daily`.
2) Uruchom lint/testy lokalnie (`ruff`, `pytest -q`) i upewnij się, że zielone.
3) Commit/push na `work/daily`.
4) CI:
   - `Tests` (pip + python) bieg na `work/daily` i `main`.
   - Cięższe `ci-gates` — na PR/main (enforce bramki).
5) Promocja: zmerguj/synchronizuj `work/daily` → `main` po zielonych przebiegach.

Public-only CI: `.github/workflows/ci_public.yml` (runs when repo is public).
Private-only build: `.github/workflows/build_private.yml` (runs when repo is private).

Self-hosted runner: see `infra/runner/` (docker compose with ephemeral runner).

PAT rotacja (przypominajka)

- Personal Access Token (ADMIN_TOKEN) rotujemy co 30-90 dni.
- Po rotacji zaktualizuj `.devkeys/admin_token.txt` lub odśwież `gh auth` (scope: repo/workflow).
