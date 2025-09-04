<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: docs/runbooks/w2_boundary_supply_chain.md            |
| ROLE: Docs runbook.                                          |
| PLIK: docs/runbooks/w2_boundary_supply_chain.md            |
| ROLA: Runbook dokumentacji.                                  |
+-------------------------------------------------------------+
-->

# W2 — Boundary & Supply‑chain (Runbook)

## Cel
- Boundary: obserwacja shardów i rekonstrukcja (delta_bits == 0 w bramce).
- Supply‑chain: SBOM + provenance, egzekwowane w ci‑gates (deny‑by‑default).

## Kroki lokalne
- UI: otwórz `clients/web/public/boundary.html` (przycisk „Reconstruct now”).
- API (in‑proc):
  - `GET /v1/boundary/status` — status shardów z `anchors.observed_at`.
  - `POST /v1/boundary/reconstruct` — świeży odczyt (bez efektów ubocznych).
- Smoke/dema:
  - `uv run --group dev python scripts/smokes/w2_boundary_demo.py` — status, reconstruct, compute raport i gate.

## CI — egzekwowanie
- Workflow: `.github/workflows/ci-gates.yml`:
  - `Generate SBOM (CycloneDX JSON)` → `sbom.json`.
  - `Build provenance (in-toto style)` → `out/provenance.json`.
  - `Enforce supply-chain (deny-by-default)` — wymaga obecności `sbom.json` lub `artifact.json`.
  - `Require cosign attestations (optional)` — ustaw `vars.REQUIRE_COSIGN_ATTESTATIONS=1` aby wymusić obecność `sbom.json.sig` i `sbom.json.cert` (sprawdzane przez `scripts/supply_chain/verify_cosign_artifacts.py`).

## DOD
- Boundary‑Gate: `delta_bits == 0` i `bits_delta_map[*] == 0` (strict) — czerwony gdy naruszenie.
- Supply‑chain: brak SBOM/provenance → gate FAIL (ci‑gates).

## Uwagi operacyjne
- Katalog pakietów PCO: `data/public_pco/` (shard‑aware); można nadpisać przez `PROOF_BUNDLE_DIR`.
- Raport rekonstrukcji: `out/boundary_report.json` (lokalny artefakt smoke).
- Wymagane narzędzia CI instalowane on‑the‑fly (`cyclonedx-py`, `cyclonedx-bom`).

