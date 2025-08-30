# CERTEUS <img src="docs/assets/brand/certeus-favicon.svg" height="24" alt="CERTEUS" />

[![CI](https://github.com/ORG/REPO/actions/workflows/ci.yml/badge.svg)](https://github.com/ORG/REPO/actions)
[![SemVer](https://img.shields.io/badge/semver-1.x-blue)](#versioning-deprecation-support)
[![SLSA](https://img.shields.io/badge/slsa-3%2B-8A2BE2)](https://slsa.dev)
[![OpenSSF Scorecard](https://img.shields.io/badge/openssf-scorecard-brightgreen)](https://securityscorecards.dev/)
[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)

<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="docs/assets/brand/certeus-banner-dark.png">
    <source media="(prefers-color-scheme: light)" srcset="docs/assets/brand/certeus-banner-light.png">
    <img alt="CERTEUS — Proof-native AI System" src="docs/assets/brand/certeus-readme-banner.svg" />
  </picture>
</p>

> **Proof-native system dla dowodów, decyzji i modeli.** Rdzeń _niezmienialny_ (PCO/Boundary), wszystko inne – _wtyczki_ i _polityki_.
>
> **Fizyka sensu:** CFE (geometria), lexqft (ścieżki), QTMP (pomiar). **Interfejsy 1. klasy:** MailOps, ChatOps.
> (Technikalia: Manifest Jednolity v1.5 w `docs/manifest.md`.)

---

## Spis treści

- [Dlaczego CERTEUS?](#dlaczego-certeus)
- [Architektura (1 obraz)](#architektura-1-obraz)
- [Szybki start (Dev/SRE/Audytor)](#szybki-start-devsreaudytor)
- [ChatOps — pierwsza komenda](#chatops--pierwsza-komenda)
- [MailOps — ingest i PFS://](#mailops--ingest-i-pfs)
- [Cookbooki domenowe](#cookbooki-domenowe)
- [API — 10 najważniejszych endpointów](#api--10-najważniejszych-endpointów)
- [Gwarancje i bramki CI/SLO](#gwarancje-i-bramki-cislo)
- [Bezpieczeństwo & łańcuch dostaw](#bezpieczeństwo--łańcuch-dostaw)
- [Observability & Runbooks](#observability--runbooks)
- [Konfiguracja / ENV](#konfiguracja--env)
- [Struktura repo](#struktura-repo)
- [Standard kodowania](#standard-kodowania)
- [Brand & Assets](#brand--assets)
- [Versioning, Deprecation, Support](#versioning-deprecation-support)
- [FAQ](#faq)
- [Glosariusz](#glosariusz)
- [Licencja](#licencja)

---

## Dlaczego CERTEUS?

- **Proof-Only I/O**: każdy wynik publikowalny musi nieść **PCO** (Proof-Carrying Output); inaczej — **DROP**.
- **Boundary = audyt natychmiastowy**: stan systemu rekonstruowalny z „brzegu” (append-only), docelowo `delta_bits == 0`.
- **Fizyka sensu**: CFE/lexqft/QTMP zamiast „heurystyk”. Geodezyjny dowód, horyzont zdarzeń evidencyjnych, nieoznaczoność operatorów.
- **Modułowość**: _Domain Packs_ (Prawo/Finanse/Kod/Sec/Med), _Devices_ (HDE/Q-Oracle/Entangler/Chronosync).
- **Enterprise**: PQ-crypto (Ed25519 + ML-DSA), FROST 2-z-3, SLSA/in-toto/SBOM, TEE (Bunkier).

---

## Architektura (1 obraz)

```
Core → Services → Modules → Plugins (Domain Packs) → Clients → Infra
```

- **Core**: Truth Engine, PCO SDK, Crypto, Contracts
- **Services**: ProofGate, Ledger, Boundary, Context Forge, MailOps, ChatOps
- **Modules**: CFE, lexqft, QTMP, ethics (Equity-Meter/HHE)
- **Plugins**: packs-law / packs-fin / packs-code / packs-sec / packs-med
- **Clients**: CERT-Cockpit (Web/Desktop/Mobile)
- **Infra**: CI/SLO-Gates, k8s, OTel, Grafana

> Szczegóły: patrz „Manifest v1.5” w `docs/manifest.md`.

---

## Szybki start (Dev/SRE/Audytor)

> Ustal bazowy adres usług:

```bash
export CER_BASE="http://localhost:8081"
```

### Dev (lokalnie)

```bash
# Linux/macOS
uv venv && source .venv/bin/activate
uv pip install -r requirements.txt
docker compose -f infra/docker-compose.dev.yml up -d --build
uvicorn services.proofgate.app:app --reload --port 8081
uvicorn services.boundary_service.app:app --reload --port 8082
```

```powershell
# Windows PowerShell
uv venv; .\.venv\Scripts\Activate.ps1
uv pip install -r requirements.txt
docker compose -f infra/docker-compose.dev.yml up -d --build
python -m uvicorn services.proofgate.app:app --reload --port 8081
```

### SRE (k8s)

```bash
kubectl apply -f infra/k8s/core.yaml
kubectl apply -f infra/k8s/services.yaml
kubectl apply -f infra/k8s/ingress.yaml
```

### Audytor (weryfikacja PCO)

```bash
cerctl ledger get CER-1 | jq '.proof, .claims[0]'
cerctl boundary reconstruct --date 2025-08-30
```

---

## ChatOps — pierwsza komenda

```bash
curl -sX POST "$CER_BASE/v1/chatops/command"   -H 'Content-Type: application/json'   -d '{ "cmd":"cfe.geodesic --case CER-42", "text_context":"demo" }' | jq
# oczekiwane: {"result":{...},"pco":{...}}
```

## MailOps — ingest i PFS://

```bash
curl -sX POST "$CER_BASE/v1/mail/ingest"   -H 'Content-Type: application/json'   -d '{ "raw_mime_b64":"..."}' | jq '.attachments, .evidence_ref'
# Załącznik dostępny jako pfs://mail/<messageId>/<attachment>
```

---

## Cookbooki domenowe

### Prawo (LEXENITH)

```bash
# Geodezyjny dowód
curl -sX POST "$CER_BASE/v1/cfe/geodesic" -d '{"case":"CER-LEX-7"}' | jq
# Horyzont zdarzeń dowodowych (lock)
curl -sX POST "$CER_BASE/v1/cfe/horizon" -d '{"case":"CER-LEX-7"}' | jq
```

### Finanse (FINENITH „Quantum Alpha”)

```bash
# Pomiar na superpozycji (R/S operators)
curl -sX POST "$CER_BASE/v1/fin/alpha/measure" -d '{"pair":"BTC/USD"}' | jq
# Splątania aktywów
curl -s "$CER_BASE/v1/fin/alpha/entanglements" | jq
```

### Security (ProofFS / artefakty)

```bash
# Montaż pfs:// tylko-do-odczytu (kontener sidecar lub host)
# przykładowy skrypt: scripts/prooffs/mount_ro.sh (placeholder)
```

---

## API — 10 najważniejszych endpointów

```text
POST /v1/proofgate/publish          # decyzja publikacji + PCO + wpis do ledger
GET  /v1/ledger/{case_id}           # odczyt public payload
POST /v1/boundary/reconstruct       # Boundary == 0 delta (append-only)
POST /v1/cfe/geodesic               # geodezyjny dowód (CFE)
POST /v1/cfe/horizon                # horyzont zdarzeń dowodowych (CFE)
POST /v1/qtm/measure                # kolaps funkcji falowej (QTMP)
POST /v1/lexqft/tunnel              # tunelowanie dowodowe
POST /v1/mail/ingest                # ingest e-maila → Evidence DAG/PFS
POST /v1/chatops/command            # komenda tekstowa → wywołanie usług
POST /v1/devices/horizon_drive/plan # plan dowodów do horyzontu (HDE)
```

---

## Gwarancje i bramki CI/SLO

- **Gauge-Gate:** `gauge.holonomy_drift ≤ 1e-3`
- **Path-Coverage (lexqft):** `coverage_gamma ≥ 0.90`, `uncaptured_mass ≤ 0.05`
- **Boundary-Rebuild:** `delta_bits == 0` (raport `bits_delta_map`)
- **Supply-chain:** SBOM + in-toto + cosign **wymagane** (deny-by-default)
- **SLO**: p95 latencja API, error-budget, alerty \*\*multi-burn-rate`

> Bramka publikacji: **Proof-Only** — brak PCO ⇒ DROP.

---

## Bezpieczeństwo & łańcuch dostaw

- **PQ-crypto**: Ed25519 + ML-DSA (hybrydowo), **FROST 2-z-3**
- **TEE (Bunkier)**: TDX/SEV-SNP/SGX + attestation w ProofGate
- **SLSA 3+ / in-toto / SBOM CycloneDX / cosign / trivy**
- **OPA/Rego**: polityki dostępu, role **AFV/ASE/ATC/ATS/AVR**

---

## Observability & Runbooks

```bash
# monitoring lokalny
docker compose -f infra/docker-compose.monitoring.yml up -d
```

- OTel tracing, eBPF profiling, Pyroscope/Parca
- Runbooks: `docs/runbooks/` – Boundary stuck, Gauge drift, PCO revoke

---

## Konfiguracja / ENV

- `CER_PROOF_STRICT=true` (Proof-Only Sockets)
- `CER_BOUNDARY_BUCKET=s3://...` (WORM)
- `CER_CRYPTO_MODE=hybrid` (Ed25519+ML-DSA)
- `CER_TEE_REQUIRED=false|true` (profil Bunkier)
- `CER_BASE=http://localhost:8081` (bazowy URL dla przykładów)

Pełna lista: `docs/configuration.md`

---

## Struktura repo

```
core/       services/    modules/    plugins/     clients/    schemas/    policies/
ci/         infra/       scripts/    docs/
```

---

## Standard kodowania

Zob. `docs/manifest.md` — sekcja **21) Premium Code Style** (baner, docstring PL/EN, PNIP/PCO, OTel, testy, linty).
Przykłady w: Python/TS/Go/Rust/Bash/HTML/YAML/JSON/SQL.

---

## Brand & Assets

- Pliki trzymamy w `docs/assets/brand/` i `clients/web/public/brand/`.
- README używa `<picture>` z wariantami dark/light i fallbackiem SVG.
- Social preview: `docs/assets/brand/certeus-og.png` (1200×630) – ustaw w **Repo → Settings → Social preview**.

Struktura:

```
docs/assets/brand/
  certeus-banner-dark.png
  certeus-banner-light.png
  certeus-readme-banner.svg
  certeus-favicon.svg
  certeus-og.png
clients/web/public/brand/
  favicon.svg
  apple-touch-icon.png
  site.webmanifest
```

---

## Versioning, Deprecation, Support

- **SemVer** (major.minor.patch) + wersjonowanie **PCO schema** (`pco.vX.Y`).
- **Deprecation policy**: 1 wersja major „overlap”; ostrzeżenia w ChatOps/ProofGate.
- **Support**: Enterprise SLA (p1/p2/p3), targety SLO w `docs/sla.md`.

---

## FAQ

**1. Czemu moja odpowiedź nie wychodzi?**
Bo jest **Proof-Only** — brak PCO ⇒ `DROP`. Użyj `POST /v1/proofgate/publish`.

**2. „Gauge drift > ε” — co to znaczy?**
Naruszyłeś niezmienniczość sensu przy transformacjach (język/jurysdykcja/rewizja). Sprawdź mapowania Ω-Kernel.

**3. Jak audytować bez zaufania?**
`cerctl ledger get <CASE>` + `boundary reconstruct` + weryfikacja podpisów PCO (hybryda + FROST).

---

## Glosariusz

**PCO** – Proof-Carrying Output • **PNIP** – Proof-Native Ingress Payload • **Ω-Kernel** – rejestr transformacji
**Boundary** – append-only „brzeg” systemu • **CFE/lexqft/QTMP** – fizyka sensu • **HDE/Q-Oracle/Entangler/Chronosync** – devices
**Domain Pack** – wtyczka dziedzinowa (Prawo/Finanse/…) • **ProofFS** – read-only FS z Merkle-dowodami

---

## Licencja

MIT © 2025 CERTEUS Contributors
