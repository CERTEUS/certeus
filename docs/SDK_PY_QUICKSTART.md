#!/usr/bin/env markdown

# CERTEUS — Python SDK (MVP)

Minimalny klient Python do wybranych endpointów QTMP i lexqft. Brak dodatkowych zależności poza `requests`.

## Instalacja (lokalna ścieżka)

```python
from sdk.python.certeus_sdk import CerteusClient

cli = CerteusClient(base_url="http://127.0.0.1:8000")

# QTMP: init + measure
cli.qtm_init_case(case="LEX-001", basis=["ALLOW","DENY","ABSTAIN"])  # predistribution
resp = cli.qtm_measure(operator="L", case="LEX-001", source="sdk:quickstart")
print(resp.ok, resp.status, resp.data, resp.pco_headers)

# Measure sequence
seq = cli.qtm_measure_sequence(operators=["L","T"], case="LEX-001")
print(seq.data)

# Operators / Uncertainty / Decoherence
print(cli.qtm_operators().data)
print(cli.qtm_uncertainty().data)
cli.qtm_decoherence(case="LEX-001", channel="dephasing", gamma=0.1)

# lexqft
print(cli.lexqft_coverage().data)
print(cli.lexqft_tunnel(evidence_energy=1.1).data)

# Presets
cli.qtm_preset_save(case="LEX-001", operator="T")
print(cli.qtm_preset_get(case="LEX-001").data)
print([p for p in (cli.qtm_preset_list().data or [])])
cli.qtm_preset_delete(case="LEX-001")

# Ledger
print(cli.ledger_records(case_id="LEX-001").data)

# ChatOps
print(cli.chatops_command(cmd="qtm.measure", args={"operator": "L", "case": "LEX-001"}).data)
```

Uwaga: PCO przekazywane jest w nagłówkach `X-CERTEUS-PCO-*` i zwracane w polu `pco_headers` obiektu `SDKResponse`.

— CERTEUS
