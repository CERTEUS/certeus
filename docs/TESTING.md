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

