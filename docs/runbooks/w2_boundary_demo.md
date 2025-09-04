<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/w2_boundary_demo.md                    |
| ROLE: Runbook (W2 Boundary demo).                            |
| PLIK: docs/runbooks/w2_boundary_demo.md                    |
| ROLA: Runbook (Demo tygodnia 2 — Boundary).                  |
+-------------------------------------------------------------+
-->

# W2 — Boundary Demo (zakładka + reconstruct)

Cel: pokazać widok shardów, delta bits oraz wywołanie „Reconstruct now” z kotwicami czasu i linkiem do Ledger.

## UI

Otwórz: `http://127.0.0.1:8000/app/public/boundary.html`

- Przycisk „Reconstruct now” wywołuje `POST /v1/boundary/reconstruct`.
- Tabela przedstawia `Δbits`, liczebność plików i kompresję.
- Link do Ledger: `/v1/ledger/{case_id}/records`.

## API (cURL)

```
curl -s http://127.0.0.1:8000/v1/boundary/status | jq .
curl -s -X POST http://127.0.0.1:8000/v1/boundary/reconstruct | jq .
```

## Gate

- Gate `Boundary-Rebuild` pobiera raport i sprawdza `delta_bits == 0` per shard (lub tolerancję, gdy skonfigurowano).
- Raport: `scripts/gates/boundary_rebuild_gate.py` oraz skrypt `scripts/gates/compute_boundary_report.py`.

## KPI (W2)

- UI działa i pokazuje agregaty.
- Reconstruct zwraca odpowiedź 2xx i aktualizuje statystyki.
- Gate raportuje „zielono” przy stabilnym stanie.

