# 90 dni — Raport pokrycia (W1–W18)

Status: główne bramki i kontrakt API zielone (Smoke, ci-gates, CI-Public). Poniżej mapping tygodni i status (domknięte; resztówki przeniesione do vNext — patrz `docs/reports/90dni_final_status.md`).

- W1: CI/gates/Proof-Only I/O — OK (asset-guard, gauge, path-coverage, boundary; Proof-Only middleware; SLO/perf smoke)
- W2: Boundary & PNIP - OK (PNIP strict + testy OK; resztówki migrowane do vNext — supply-chain attestacje; Cockpit „Reconstruct now”).
- W3: CFE v0.1 — OK (geodesic/horizon API + gate)
- W4: QTMP v0.1 — OK (init/measure/commutator/find_entanglement)
- W5–W9: Cockpit/Flows — Partial/OK (widoki i endpointy obecne; pełne flows do dopracowania)
- W10: Observability & SRE - OK (SLO/perf/OTEL OK; DR-drills/canary przeniesione do vNext).
- W11: Performance — OK (quick_bench + gate/regresja)
- W12: Compliance & Data Gov - OK (checklisty i pola PNIP/PCO obecne; DPIA/PII-safe flows przeniesione do vNext).
- W13: Devices v0.2 - OK (API/metryki są; rozszerzenia przeniesione do vNext).
- W14–W15: OpenAPI/Compat — OK (parity + compat w info)
- W16-W18: Stabilizacja/Release - OK (release pipeline przeniesiony do vNext — osobna inicjatywa wydawnicza).

Zadania domykające zmapowane do Issues i przeniesione do: docs/reports/90dni_closure_tasks.md (zamknięty — z odnośnikami do Issues)
