# CERTEUS SDK (Python)

Prosty klient HTTP do CERTEUS.

Instalacja (lokalnie z repo):

```
pip install requests
```

Użycie:

```python
from clients.python.certeus_sdk import CerteusClient

cli = CerteusClient(base_url="http://127.0.0.1:8000", tenant_id="demo")
print(cli.health())
print(cli.openapi()["info"])  # zawiera x-compat i x-release

# Publiczne PCO (zero PII)
pcop = cli.get_public_pco("case-001")
print(pcop)
```

