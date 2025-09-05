## Security Policy

Zależy nam na bezpieczeństwie użytkowników i danych. Poniżej zasady, wymagania i procedury.

### Zgłaszanie podatności

- Kontakt: skarzyckiradoslaw@gmail.com (PGP mile widziane).
- Responsible disclosure: prosimy o niepublikowanie 0‑day; standardowe okno na naprawę to 90 dni (lub szybciej dla krytycznych).
- Do zgłoszenia dołącz: wersja/commit SHA, minimalny reproduktor, logi, PCO/artefakty (jeśli dotyczy), kontekst środowiska.

### Proof‑Only I/O (Ingress/Clients)

- Produkcyjnie włączone: `STRICT_PROOF_ONLY=1`.
- Algorytm tokenów: JWS EdDSA (Ed25519). Nagłówek `Authorization: Bearer <JWS>` lub `X-PCO-Token`.
- Walidacja kluczy publicznych: `/.well-known/jwks.json` (OKP/Ed25519) lub ENV `PCO_JWKS_B64URL`/`ED25519_PUBKEY_B64URL`.
- Klienci egress: podpisy Ed25519 (`ED25519_SECRET_B64URL`), możliwy ProofHttpxClient lub pco_token_tool.

### Supply‑chain & Artefakty

- Wymagamy: SBOM (CycloneDX) + provenance (in‑toto style).
- Podpisy: cosign (keyless, Fulcio/Rekor). W CI podpisujemy i weryfikujemy (verify‑blob) SBOM i provenance.
- Polityki verify (opcjonalne, zalecane):
  - `COSIGN_EXPECT_ISSUER=https://token.actions.githubusercontent.com`
  - `COSIGN_EXPECT_URI_CONTAINS=<repo-url>` (np. `https://github.com/ORG/REPO`)
- Weryfikacja powinna odrzucać artefakty bez oczekiwanych cech (issuer/URI).

### Skan zależności i zasady

- Trivy FS skanuje repo (CRITICAL/HIGH → fail w CI; deny‑by‑default).
- SLSA 3+ / in‑toto / SBOM w łańcuchu dostaw.

### Role i polityki

- OPA/Rego (deny‑by‑default), role: AFV/ASE/ATC/ATS/AVR.
- Proof‑Only dla głównych interfejsów (MailOps/ChatOps/API).

### TEE / Confidential Computing

- Profil Bunkier: TDX/SEV‑SNP/SGX + attestation w ProofGate (opcj. wg profilu wdrożenia).

### Incydenty

- Zgłaszaj niezwłocznie; dołącz logi/artefakty (PCO), zrzuty czasowe (Boundary snapshot). Triage wg powagi (p1/p2/p3) i publikacja poprawek/porad.
