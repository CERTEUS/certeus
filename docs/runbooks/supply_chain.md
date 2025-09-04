#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/supply_chain.md                         |
# | ROLE: Runbook SRE/Sec — Supply Chain                        |
# +-------------------------------------------------------------+

## Cel (W2)
- Deny-by-default dla artefaktów supply-chain w CI.
- Generacja SBOM (CycloneDX), provenance (in-toto styl) i weryfikacja.
- Opcjonalnie: wymagane attestacje cosign.

## Kroki lokalnie
1) Zainstaluj zależności (w venv): `pip install cyclonedx-bom jsonschema`.
2) SBOM (preferencja `cyclonedx-py`):
   - `cyclonedx-py --format json --output sbom.json` (fallback: `cyclonedx-bom -o sbom.json -F json`).
3) Provenance:
   - `python scripts/supply_chain/make_provenance.py` → `out/provenance.json`.
   - Walidacja: `python scripts/validate_provenance.py` (schemat: `schemas/certeus.provenance.v1.json`).
4) Attestacje (opcjonalnie):
   - Umieść artefakty `sbom.json.sig` i `sbom.json.cert` w katalogu repo.
   - Wymuś w CI poprzez `vars.REQUIRE_COSIGN_ATTESTATIONS=1`.

## CI (ci-gates.yml)
- Buduje SBOM, tworzy provenance, waliduje schemat, egzekwuje supply-chain (brak → FAIL).
- Zmienna `SUPPLY_CHAIN_ENFORCE=1` — deny-by-default.
- Attestacje cosign weryfikowane warunkowo przez `REQUIRE_COSIGN_ATTESTATIONS=1`.

## Notatki
- Brak logowania sekretów (tokeny tylko ENV / `.devkeys/*.txt` ignorowane przez git).
- Wersjonowanie schematu: `schemas/certeus.provenance.v1.json` (rozszerzalny, `additionalProperties: true`).

