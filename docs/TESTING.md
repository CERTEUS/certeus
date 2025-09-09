# Testing & Quality

How to run tests and quality checks locally.

## Python tests

```bash
pip install -r requirements.txt
pytest -q
```

Pytest configuration: `pytest.ini` (root and `certeus/pytest.ini`).

## Lint & Type Checks

```bash
ruff check .
pyright -p pyrightconfig.json
```

## Contracts & Gates

Helpful scripts:

- OpenAPI contract checks: `scripts/contracts/openapi_spec_validate.py`
- Gate runners: `scripts/gates/*`
- CI gate docs: [adr/ADR-0003-ci-gates.md](adr/ADR-0003-ci-gates.md)

## Server Smoke Test

Quick e2e check of core API endpoints using the in-process TestClient:

```bash
# full suite
pytest -q tests/e2e/test_smoke_endpoints.py

# or only core smoke
pytest -q -k smoke_endpoints
```

## Docs Dev Server

```bash
mkdocs serve -f mkdocs.yml -a 0.0.0.0:8080
# build for production
mkdocs build -f mkdocs.yml
```
