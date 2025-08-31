# Definition of Done (Manifest v1.7) — Status

This checklist mirrors section 16 of Manifest v1.7 and tracks repository status.

## A. KOD i SCHEMATY (MUST)
- [x] `services/api_gateway/schemas/proofbundle_v0.2.json` zgodny z Aneks B (w repo i używany do walidacji)
- [x] Endpointy `/v1/pco/bundle`, `/pco/public/{case_id}`, `/.well-known/jwks.json` (testy w `tests/services/`)
- [x] `policies/pco/policy_pack.yaml` (progi PCO, redakcja, role)
- [x] `monitoring/slo/slo_gate.yml` (reguły i bramki)
- [x] Moduł Law-as-Data: cache + adaptery (ISAP/Dz.U.)

## B. OBSERVABILITY/SECURITY (MUST)
- [x] Metryki + alerty krytyczne; dashboard Grafana (provisioning + dashboard JSON)
- [x] JWKS żywe; Key Manager (ENV/Vault) + integracja routera

## C. COMPLIANCE (MUST)
- [x] Matryca AI Act (high‑risk) + DPIA (docs/compliance)
- [x] Procedura ABSTAIN: fail‑closed w ProofGate, eskalacja do Counsel (policy “counsel” podpis wymagany)

## D. REPRODUCIBILITY (MUST)
- [x] SBOM/SLSA workflow w CI (supply‑chain.yml)
- [~] OCI image `image` + `image_digest` w ProofBundle (zapisane pola; publikacja do rejestru poza zakresem repo)

## E. QA (MUST)
- [x] 0 krytycznych; testy zielone (pytest). SLO metrics aktywne; decyzje ProofGate zgodnie z policy

Legenda: [x] zrealizowane, [~] częściowo (wymaga zewnętrznego rejestru/CI/CD)

