# +-------------------------------------------------------------+

# | CERTEUS |

# +-------------------------------------------------------------+

# | FILE: CONTRIBUTING.md |

# | ROLE: Project Markdown. |

# | PLIK: CONTRIBUTING.md |

# | ROLA: Dokument Markdown. |

# +-------------------------------------------------------------+

# Contributing

Dziękujemy za wkład! Przed wysłaniem PR, sprawdź proszę:

- Lint + testy: `ruff check .` i `pytest -q` → zielone
- Premium Style (sec.21): baner CERTEUS + docstring PL/EN + sekcje `# ===`
- CI Gates:
  - Gauge-Gate: `python scripts/gates/gauge_gate.py --epsilon 1e-3`
  - Path-Coverage-Gate: `python scripts/gates/path_coverage_gate.py --min-gamma 0.90 --max-uncaptured 0.05`
  - Boundary-Rebuild-Gate: `python scripts/gates/boundary_rebuild_gate.py --report out/boundary_report.json`
- Proof-Only I/O: Artefakty publikowalne muszą zawierać PCO (bez PII)

## Jak uruchomić lokalnie (skrót)

```powershell
py -3.11 -m venv .venv; .\.venv\Scripts\Activate.ps1
$py = ".\.venv\Scripts\python.exe"
& $py -m pip install -U pip wheel setuptools ruff pytest
& $py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
```
