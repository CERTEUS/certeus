# Zadania domykające W1–W18 (90_dni_work)

- W2 - Boundary & PNIP
  - [x] Supply-chain attestacje: wygenerować SBOM, podpisać artefakty (cosign), dodać verify step dla PR (deny-by-default) → Issue: https://github.com/CERTEUS/certeus/issues/58
  - [x] Cockpit Boundary: dodać akcję "Reconstruct now" i odświeżanie raportu gate'u → Issue: https://github.com/CERTEUS/certeus/issues/59

- W10 - Observability & SRE
  - [x] DR-drills: przygotować skrypt chaos testu shardu (Boundary), raportować RTO/RPO do out/ → Issue: https://github.com/CERTEUS/certeus/issues/60
  - [x] Canary/progressive: dodać przykład flagi/rolloutu i gate'y dla rollout health → Issue: https://github.com/CERTEUS/certeus/issues/61

- W12 - Compliance & Data Gov
  - [x] DPIA: przygotować checklistę i runbook (docs/compliance/dpia.md) + smoke ścieżki odwołań (right-to-be-forgotten) → Issue: https://github.com/CERTEUS/certeus/issues/62
  - [x] Redaction policy: twarde egzekwowanie reguł w PFS (ponad stub), testy E2E PII-safe → Issue: https://github.com/CERTEUS/certeus/issues/63

- W13 - Devices v0.2
  - [x] Uzupełnić scenariusze entangle/chronosync (metryki przypadku), testy property → Issue: https://github.com/CERTEUS/certeus/issues/64

- Stabilizacja release
  - [x] Przygotować release pipeline (GHCR + SBOM + publikacja PCO), przywrócić gałąź/PR po GO → Issue: https://github.com/CERTEUS/certeus/issues/65

Status: Zamknięto plan 90 dni — resztówki przeniesione do vNext (Issues powyżej). 
