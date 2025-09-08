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

Wynik: PENDING (wypełnić po audycie)

## Kryteria G1 (checklista)
- [ ] ci‑gates zielone (Smoke ubuntu/windows + `ci-gates`)
- [ ] PCO v0.3 przyjęte + testy E2E PASS
- [ ] VALIDATE_PCO (SEC‑PCO) — report‑only włączone, bez krytycznych ostrzeżeń
- [ ] Governance: OPA roles + Governance Pack — spójne, gate PASS
- [ ] SLO/Perf: smoki PASS; brak krytycznych regresji p95
- [ ] Marketplace Policy Gate / Pack ABI/SemVer Gate — PASS (report‑only)
- [ ] SBOM + provenance artefakty obecne i zweryfikowane (report‑only)
- [ ] OpenAPI contract lint/smoke PASS
- [ ] A11y/i18n baseline PASS
- [ ] Dokumenty governance (roadmapa, RACI, risks, VERSIONING, ADR, G1_pre_review) — kompletne

## Artefakty i dowody
- Raporty perf/SLO: `out/perf_bench.json`, `out/slo_metrics.json`
- SBOM/provenance: artefakty CI
- Boundary snapshot/diff: `out/boundary_report.json`
- Log ci‑gates: załącznik do PR

## Jak uruchomić (skrót)
- Lint/Testy: `python -m ruff check . --fix && python -m ruff format . && python -m pytest -q`
- CI local (skróty): patrz `docs/runbooks/ci_local.md`

## Podpisy
- A0: …  Data: …   Decyzja: PASS/FAIL
- A4: …  A5: …  A6: …  A9: …

