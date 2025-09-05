# A11 — CI/Workflows sanitize (parallel stream)

Scope:
- .github/workflows/** (ci-gates, smoke, openapi-pages, promote-*, security-*)
- scripts/** only when used by workflows (no runtime API)

Tasks:
- [x] Remove control chars, tabs; normalize EOL to LF
- [x] Fix heredoc indent; validate with `yamllint`/PyYAML locally
- [x] Unify Python setup (3.11) + pip/uv caching strategy
- [x] Fix invalid `needs` and duplicate steps; tighten continue-on-error only for report-only gates
- [x] Ensure required check names match Branch Protection (Tests/UI Smoke/Canary-Gate/truth-gates)
- [x] Add lightweight self-check (OpenAPI generate + Spectral) non-blocking

DOD:
- [x] PR to work/daily green: Tests, UI Smoke, Canary-Gate, truth-gates
- [x] Push on main triggers ci-gates without workflow file errors

Do not touch:
- services/**, tests/** (except CI-only helpers)
