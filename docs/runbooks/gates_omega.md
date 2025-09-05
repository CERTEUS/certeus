# Runbook — Ω‑Kernel Drift (Gauge + Domain Map)

"""
PL: Jak uruchamiać i interpretować metryki Ω‑Kernel (gauge/omega/omega_mapped).
EN: How to run and interpret Ω‑Kernel metrics (gauge/omega/omega_mapped).
"""

## Szybki start

```bash
python scripts/gates/compute_gauge_drift.py \
  --out out/gauge.json \
  --before-file samples/before.txt \
  --after-file samples/after.txt \
  --domain sec \
  --max-jaccard-mapped 0.3
```

Artefakt: `out/gauge.json` zawiera:

- `gauge.holonomy_drift` — zebrane z `/v1/cfe/curvature` (jeśli dostępne) lub in‑proc.
- `omega.*` — surowe metryki Ω‑Kernel na tekście wejściowym (jaccard/entropy/entity drift).
- `omega_mapped.*` — metryki po `domain_map` (med|sec|code), gdy `--domain` ustawione.

## Progi i egzekwowanie

- Surowe: `--max-jaccard|--max-entropy|--max-entity-jaccard` lub odpowiednie ENV.
- Mapped: `--max-*-mapped` lub ENV: `OMEGA_MAX_JACCARD_MAPPED`, `OMEGA_MAX_ENTROPY_MAPPED`, `OMEGA_MAX_ENTITY_DRIFT_MAPPED`.
- Egzekwowanie mapped: ustaw `ENFORCE_OMEGA_MAPPED=1` (domyślnie report‑only).

## Dobre praktyki

- Dla pipeline’ów MED/SEC/CODE raportuj `omega_mapped` — drift powinien być niższy/stabilniejszy.
- Nie mieszaj translacji międzyjęzykowych — `domain_map` to kanon w obrębie domeny, nie tłumaczenie.
- W testach używaj property‑based (Hypothesis) do weryfikacji idempotencji i stabilności liczby tokenów.

