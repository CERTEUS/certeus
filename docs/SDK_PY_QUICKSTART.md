#!/usr/bin/env markdown

# CERTEUS — Python SDK (MVP)

Minimalny klient Python do wybranych endpointów QTMP i lexqft. Brak dodatkowych zależności poza `requests`.

## Instalacja (lokalna ścieżka)

```python
from sdk.python.certeus_sdk import CerteusClient

# (opcjonalnie) nagłówki globalne, np. tenant
cli = CerteusClient(base_url="http://127.0.0.1:8000", headers={"X-Tenant-ID": "t-demo"})

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

    # Commutators / Expectation
    print(cli.qtm_commutator(A="L", B="T").data)
    print(cli.qtm_expectation(case="LEX-001", operator="W").data)

    # lexqft
    print(cli.lexqft_coverage().data)
    print(cli.lexqft_tunnel(evidence_energy=1.1).data)

    # Presets
    cli.qtm_preset_save(case="LEX-001", operator="T")
    print(cli.qtm_preset_get(case="LEX-001").data)
    print([p for p in (cli.qtm_preset_list().data or [])])
    cli.qtm_preset_delete(case="LEX-001")

    # State / History
    print(cli.qtm_state(case="LEX-001").data)
    print(cli.qtm_history(case="LEX-001").data)
    print(cli.qtm_state_delete(case="LEX-001").data)

# Ledger
print(cli.ledger_records(case_id="LEX-001").data)

# ChatOps
print(cli.chatops_command(cmd="qtm.measure", args={"operator": "L", "case": "LEX-001"}).data)
```

Uwaga: PCO przekazywane jest w nagłówkach `X-CERTEUS-PCO-*` i zwracane w polu `pco_headers` obiektu `SDKResponse`.

— CERTEUS

## ProofGate — publikacja PCO (z rozszerzeniem SEC‑PCO)

```python
from sdk.python.certeus_sdk import CerteusClient

cli = CerteusClient(base_url="http://127.0.0.1:8000")

pco = {
    "domain": "lex",              # dla testu: lex (role enforcement SEC może być surowszy)
    "case_id": "CER-LEX-SECEXT-1",
    "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
    "sources": [{"digest": "a"*64, "retrieved_at": "2025-01-01T00:00:00Z"}],
    "derivations": [{"solver": "z3", "proof_format": "LFSC", "artifact_digest": "b"*64}],
    "reproducibility": {"image": "img:dev", "image_digest": "sha256:deadbeef", "seed": "0"},
    "signatures": [{"role": "producer"}, {"role": "counsel"}],
    "tee": {"attested": True},    # zgodne z profilem Bunkra, jeśli aktywny
    "security": {                   # rozszerzenie SEC‑PCO (schemat v0.1)
        "finding_id": "SEC-0001",
        "severity": "HIGH",
        "status": "OPEN",
        "controls": ["ISO27001:A.12.6"],
        "evidence": [{
          "digest": "sha256:" + ("a"*64),
          "type": "artifact",
          "uri": "pfs://mail/MSEC/rep.pdf"
        }],
        "cwe": ["CWE-79"],
        "cve": ["CVE-2025-0001"],
        "cvss": 8.2,
    },
}

resp = cli.proofgate_publish(pco=pco, budget_tokens=10)
print(resp.status, resp.data)
# Oczekiwane: status "PUBLISH" oraz pole ledger_ref w odpowiedzi
```

Uwaga: w DEV/CI domyślnie włączona jest walidacja `VALIDATE_PCO=1` (report‑only),
która loguje ostrzeżenia dla rozszerzeń PCO (SEC/DPCO/MCO), nie wpływając na decyzję.

## ProofFS — exists/list dla URI `pfs://…`

```python
from sdk.python.certeus_sdk import CerteusClient

cli = CerteusClient(base_url="http://127.0.0.1:8000")

# Sprawdź istnienie artefaktu
print(cli.pfs_exists(uri="pfs://mail/MSEC/rep.pdf").data)

# Lista dla prefiksu (rekurencyjnie, filtr prosty po rozszerzeniu)
print(cli.pfs_list(prefix="pfs://mail/MSEC", recursive=True, mime="pdf").data)
```

Schemat SEC‑PCO: `schemas/security_pco_v0.1.json`. Do szybkiego smoke można
ustawić `PROOFS_FS_MATERIALIZE=1` i użyć endpointu `/v1/mailops/ingest`, który
materializuje pliki w `data/proof_fs/`.
