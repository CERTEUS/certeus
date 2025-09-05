# +-------------------------------------------------------------+

# | CERTEUS |

# +-------------------------------------------------------------+

# | FILE: docs/onboarding.md |

# | ROLE: Project Markdown. |

# | PLIK: docs/onboarding.md |

# | ROLA: Dokument Markdown. |

# +-------------------------------------------------------------+

# Onboarding — First 30 Minutes

## Dev

- Zainstaluj Python 3.11, `py -3.11 -m venv .venv`
- `pip install -U pip wheel setuptools ruff pytest`
- Start API: `uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`
- Smoke: `pwsh -File .\scripts\smoke_api.ps1` lub `bash ./scripts/smoke_api.sh`

## SRE

- `docker compose -f infra/docker-compose.monitoring.yml up -d`
- Grafana: http://localhost:3000, Prometheus: http://localhost:9090

## Auditor

- Pobierz PCO: `curl -s http://127.0.0.1:8000/pco/public/RID-EXAMPLE`
- Zweryfikuj: `python scripts/verify_bundle.py`

## Legal / Compliance

- Manifest: `docs/manifest.md` (źródło prawdy)
- OpenAPI: `docs/openapi/certeus.v1.yaml` / `/openapi.json`
- Security Policy: `SECURITY.md`
