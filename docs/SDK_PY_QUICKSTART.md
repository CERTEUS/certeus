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

# lexqft
print(cli.lexqft_coverage().data)
print(cli.lexqft_tunnel(evidence_energy=1.1).data)
```

Uwaga: PCO przekazywane jest w nagłówkach `X-CERTEUS-PCO-*` i zwracane w polu `pco_headers` obiektu `SDKResponse`.

— CERTEUS

