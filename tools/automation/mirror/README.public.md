# CERTEUS — Public Mirror

Welcome to the public, sanitized mirror of the CERTEUS core.

This repository contains an allowlisted subset of the original project suitable for public browsing, evaluation, and discussion. Sensitive assets and proprietary materials are excluded by design.

## Status & Badges

- Build: ![CI-Public](https://github.com/CERTEUS/certeus-public/actions/workflows/ci_public.yml/badge.svg?branch=main)
- Tests: ![Tests](https://github.com/CERTEUS/certeus-public/actions/workflows/tests.yml/badge.svg?branch=main)
- Docs: ![Docs-Site](https://github.com/CERTEUS/certeus-public/actions/workflows/docs-site.yml/badge.svg?branch=main)
- Coverage: ![Coverage](https://raw.githubusercontent.com/CERTEUS/certeus-public/main/docs/badges/coverage.svg)
- License: AGPL-3.0

## Quickstart (60s)

1) Clone: `git clone https://github.com/CERTEUS/certeus-public.git`
2) Python: `python -m pip install -U pip` then `pip install -e .` (dev: `-e .[dev]`)
3) Run API: `python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`
4) Open Docs: https://certeus.github.io/certeus-public

## Architecture

- C4 overview and diagrams live in `docs/` and on Pages.
- Observability dashboards: see `observability/` and Docs.

## Links

- Docs: https://certeus.github.io/certeus-public
- API (OpenAPI): `docs/api/openapi.yaml`
- Releases: https://github.com/CERTEUS/certeus-public/releases
- Roadmap: see README in main repo and project boards.

---
Note: This mirror is auto-published from a private upstream via an allowlist and automated checks (secret scan, policy gates).
