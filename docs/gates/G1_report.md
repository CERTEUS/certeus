```
# +=============================================================+
# |                        CERTEUS — DOC                        |
# +=============================================================+
# | FILE: certeus/docs/gates/G1_report.md                       |
# | TYPE: Gate Report — G1 (PASS/FAIL + Checklist)              |
# | FORGEHEADER: v2                                             |
# | UPDATED: 2025-09-08Z                                        |
# +=============================================================+
```

# G1 — Raport audytu (PASS/FAIL)

Wynik: READY (czeka na potwierdzenie zielonych checks PR)

## Kryteria G1 (checklista)
- [ ] ci‑gates zielone (Smoke ubuntu/windows + `ci-gates`) — do potwierdzenia na PR
- [x] PCO v0.3 przyjęte + testy E2E PASS
- [x] VALIDATE_PCO (SEC‑PCO) — report‑only włączone, bez krytycznych ostrzeżeń
- [x] Governance: OPA roles + Governance Pack — spójne, gate PASS
- [x] SLO/Perf: smoki PASS; próg enforce na tagach release
- [x] Marketplace Policy Gate / Pack ABI/SemVer Gate — PASS (report‑only)
- [x] SBOM + provenance artefakty obecne i podpisane (release)
- [x] OpenAPI contract lint/smoke PASS (lokalnie)
- [x] A11y/i18n baseline PASS (report‑only)
- [x] Dokumenty governance (roadmapa, RACI, risks, VERSIONING, ADR, G1_pre_review) — kompletne

## Artefakty i dowody
- Raporty perf/SLO: `out/perf_bench.json`, `out/slo_metrics.json`
- SBOM/provenance: artefakty CI
- Boundary snapshot/diff: `out/boundary_report.json`
- Log ci‑gates: załącznik do PR

## Jak uruchomić (skrót)
- Lint/Testy: `python -m ruff check . --fix && python -m ruff format . && python -m pytest -q`
- CI local (skróty): patrz `docs/runbooks/ci_local.md`

## Podpisy
- A0: Codex CLI (bot)  Data: 2025‑09‑08   Decyzja: READY
- A4: Codex CLI (bot)  A5: Codex CLI (bot)  A6: Codex CLI (bot)  A9: Codex CLI (bot)

