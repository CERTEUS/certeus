Developer Workflow (Public tests vs Private build)

UWAGA — Zasada niezmienna (Immutable Rule)
- Publikujemy wyłącznie to, co jest jawnie dozwolone przez allowlistę LITE (mirror publiczny). Wszystko inne zostaje w repo prywatnym i przechodzi przez bramki (gitleaks/policy‑scan/branch‑protection) — bez wyjątków.
- Pełen opis: zob. `docs/AGENTS/README.md` (sekcja: Zasada niezmienna/Immutable Rule).

1) Work locally on branch `work/daily`.
2) Before end of week (W13/W14): run local lint/tests; ensure green.
3) Commit with weekly marker: include "[week-end]" or a trailer line `weekly-promote: true`.
4) Push to `work/daily`:
   - Public repo: free runners run Smoke/Tests/ci-gates.
   - Autopromotion workflow syncs `work/daily` with `main` and fast-forwards `main` if possible (no PR, no bot commits).
5) Private repo mode: build/deploy runs on self-hosted runner via `Build-Private` workflow.

Public-only CI: `.github/workflows/ci_public.yml` (runs when repo is public).
Private-only build: `.github/workflows/build_private.yml` (runs when repo is private).

Self-hosted runner: see `infra/runner/` (docker compose with ephemeral runner).

PAT rotacja (przypominajka)
- Personal Access Token (ADMIN_TOKEN) rotujemy co 30–90 dni.
- Po rotacji zaktualizuj `.devkeys/admin_token.txt` lub odśwież `gh auth` (scope: repo/workflow).
