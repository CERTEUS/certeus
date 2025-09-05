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

# Publish ProofBundle (v0.2)
ack = cli.publish_pco_bundle(
    rid="case-001",
    smt2_hash="a"*64,
    lfsc="(lfsc proof)",
)
print(ack)

# Billing (tenant=demo z nagłówka X-Tenant-ID)
print(cli.get_balance())
print(cli.allocate(10))
print(cli.refund("other-tenant", 5))
print(cli.set_quota("other-tenant", 100))
```
