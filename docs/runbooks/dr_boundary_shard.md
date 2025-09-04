#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/dr_boundary_shard.md                    |
# | ROLE: Runbook SRE — DR drill Boundary shard                 |
# +-------------------------------------------------------------+

## Cel (W4 — A8)
- Zweryfikować RTO/RPO dla Boundary przy awarii pojedynczego shardu.
- Potwierdzić, że `Boundary-Rebuild-Gate` odtwarza stan (`Δbits == 0`).

## Kroki (lokalnie/CI)
1) Przygotuj środowisko (lokalnie):
   - `PY` → aktywuj venv; uruchom API: `uvicorn services.api_gateway.main:app`.
2) Wygeneruj próbki/snapshoty:
   - `python scripts/gates/compute_boundary_report.py --out out/boundary_report.json`.
3) Zasymuluj awarię shardu i odtwórz:
   - `python scripts/gates/boundary_rebuild.py --must-zero` (egzekwuje `Δbits == 0`).
4) Gate w CI:
   - Workflow `.github/workflows/ci-gates.yml` — krok `Boundary-Rebuild` (raportuje FAIL/OK).

## Metryki i dowody
- Raport JSON: `out/boundary_report.json` (artefakt w CI).
- SLO: czas rekonstrukcji ≤ 5 s dla próbki; błąd odtworzenia `Δbits == 0`.

## Troubleshooting
- Jeśli gate FAIL:
  - Sprawdź logi: `scripts/gates/compute_boundary_report.py` i ścieżki tymczasowe.
  - Upewnij się, że wejściowe snapshoty są spójne (hashy/offsety).
  - Uruchom lokalnie z `--verbose` i porównaj `bits_delta_map`.

