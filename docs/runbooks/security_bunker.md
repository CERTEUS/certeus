# Security Bunker (TEE) — Runbook

Cel: włączenie profilu Bunkra w ProofGate i bramce CI oraz lokalne/labowe testy gotowości.

Kroki
- Ustaw zmienne repo (Actions → Variables):
  - `BUNKER=1` (włącza profil), opcjonalnie `PROOFGATE_BUNKER=1`.
  - `PQCRYPTO_READY=1` (status informacyjny w CI; nie blokuje).
- Zapewnij „atestację” (dowolny z):
  - `security/bunker/attestation.json` (parsowalny JSON w repo),
  - marker plikowy `data/security/bunker.ready`,
  - zmienna `BUNKER_READY=1` (np. w CI lub środowisku dev),
  - lub override ścieżek:
    - `BUNKER_ATTESTATION_PATH=.../attestation.json`
    - `BUNKER_MARKER_PATH=.../marker`

Weryfikacja lokalnie
```
python scripts/gates/security_bunker_gate.py   # echo status & kod wyjścia
```

W ProofGate (runtime)
- Jeśli `BUNKER=1`, endpoint `/v1/proofgate/publish` wymaga `pco.tee.attested=true` (stub) — inaczej status `ABSTAIN`.

Diagnostyka
- `BUNKER_FORCE_FAIL=1` — wymusza FAIL bramki (próby alertów/ścieżki błędu).
- Sprawdź podsumowanie kroku w CI: gate dopisuje status PQ‑crypto.

