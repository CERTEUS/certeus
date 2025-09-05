# CERTEUS Python SDK (lightweight)

Quickstart:

```python
from certeus_sdk import CerteusClient

cli = CerteusClient("http://127.0.0.1:8000", headers={"X-Tenant-ID": "t-demo"})

# Devices
plan = cli.devices_hde_plan(case="demo-lex-001", target_horizon=0.25)
qor = cli.devices_qoracle_expectation(question="Appeal?", constraints={"budget": 100})

# Marketplace
packs = cli.packs_list()
cli.packs_enable(packs[0]["name"], enabled=True)
cli.packs_install(packs[0]["name"], signature="a" * 64, version=packs[0].get("version") or "0.1.0")

# Billing
print(cli.billing_quota())
print(cli.billing_allocate(cost_units=2))
print(cli.billing_refund(units=1))

cli.close()
```

Notes:
- Uses `httpx` under the hood; set `X-Tenant-ID` header to select tenant.
- See also `docs/openapi/certeus.v1.json` for full API.

