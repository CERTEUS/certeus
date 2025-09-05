# A12 — Lint/Test hygiene (parallel stream)

Scope:
- tests/** (imports, style)
- pyproject.toml [tool.ruff] (per-file-ignores reduction)

Tasks:
- [ ] Reduce per-file-ignores; napraw `I001/E501/E402` w testach OpenAPI
- [ ] Ujednolić importy (isort via Ruff) i format
- [ ] Zredukować ostrzeżenia pytest (deprecations, duplicate op-id w testach) — bez zmiany runtime

DOD:
- [ ] `ruff check .` oraz `ruff format --check` OK
- [ ] `pytest -q` zielono bez nowych ostrzeżeń istotnych

Do not touch:
- services/** i workflows/**
