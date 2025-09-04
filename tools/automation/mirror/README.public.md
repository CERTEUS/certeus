# CERTEUS — Verifiable Cognitive Intelligence

> **Dowód, nie opinia.**  
> System, który publikuje tylko to, co można **udowodnić** — i robi to w sposób odpowiedzialny.

[![Docs-Site](https://github.com/CERTEUS/certeus-public/actions/workflows/docs-site.yml/badge.svg?branch=main)](https://github.com/CERTEUS/certeus-public/actions/workflows/docs-site.yml)
[![CI-Public-Light](https://github.com/CERTEUS/certeus-public/actions/workflows/ci_public_light.yml/badge.svg?branch=main)](https://github.com/CERTEUS/certeus-public/actions/workflows/ci_public_light.yml)
[![Policy-Scan](https://github.com/CERTEUS/certeus-public/actions/workflows/policy-scan.yml/badge.svg?branch=main)](https://github.com/CERTEUS/certeus-public/actions/workflows/policy-scan.yml)
[![License: AGPL-3.0](https://img.shields.io/badge/License-AGPL--3.0-blue.svg)](LICENSE)

## Dlaczego teraz?
- **Prawda z podpisem** – decyzje wsparte dowodami i politykami.  
- **Higiena publikacji** – zanim coś wyjdzie na świat, przechodzi bramki jakości.  
- **Minimalny front publiczny** – lśni na zewnątrz, pełna moc działa prywatnie.

## Jak to działa (w skrócie)
1. **CORE (prywatny)** – ciężkie CI/CD, kontrakty, release.  
2. **MIRROR (to repo)** – landing, assets, **Overview API**.  
3. Tygodniowo: **promocja → publikacja** (allowlista) → **squash** z autorem „Radosław Skarżycki”.

> Ślad audytowy: patrz **PROVENANCE.md** (z jakiego commita i kiedy powstał mirror).

## Sprawdź
- Strona: **https://certeus.github.io/certeus-public**  
- PROVENANCE: [PROVENANCE.md](PROVENANCE.md) (aktualny snapshot)  
- PROVENANCE historia: [PROVENANCE_HISTORY.md](PROVENANCE_HISTORY.md)

## Kontakt
- **Dyskusje / Propozycje:** https://github.com/CERTEUS/certeus-public/discussions
- **E-mail:** kontakt@certeus.pl

## Jak zacząć dyskusję (Start here)
- Wejdź w zakładkę **Discussions** i wybierz kategorię: General, Proposal lub Q&A.
- Opisz krótko temat i cel, dodaj link do fragmentu README, którego dotyczy.
- Sprawy bezpieczeństwa zgłaszaj prywatnie (security.txt): `.well-known/security.txt`.

## Polityka publikacji (LITE)
- Publicznie pokazujemy wyłącznie landing, assets, `Overview API` i pliki polityk.
- Nie publikujemy: kodu core, testów, pełnych kontraktów API, infra, coverage.
- Mirror budowany jest automatycznie z allowlisty i publikowany jako jeden squash-commit (autor: Radosław Skarżycki).
- Każde wydanie ma ślad: PROVENANCE.md (źródłowy SHA + data).
- Publikacja działa tylko, gdy `MIRROR_PUBLISH == "enabled"`.
- Wymagane checki mirrora: `Docs-Site`, `CI-Public-Light`, `Policy-Scan` (FF-only).
