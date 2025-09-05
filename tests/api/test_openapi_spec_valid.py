#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/api/test_openapi_spec_valid.py                  |

# | ROLE: OpenAPI spec validation test                           |

# | PLIK: tests/api/test_openapi_spec_valid.py                  |

# | ROLA: Test walidacji specyfikacji OpenAPI                     |

# +-------------------------------------------------------------+

"""
PL: Waliduje plik OpenAPI (docs/api/openapi.yaml) przy użyciu openapi-spec-validator.
EN: Validates OpenAPI spec (docs/api/openapi.yaml) using openapi-spec-validator.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import warnings
import yaml

# Silence deprecation warnings from openapi-spec-validator shortcuts
warnings.filterwarnings("ignore", category=DeprecationWarning)

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===


def test_openapi_spec_is_valid() -> None:
    # Lazy import to avoid ruff/isort import-order noise and keep compatibility
    try:  # support both legacy and modern versions
        from openapi_spec_validator import validate_spec as _validate  # type: ignore[attr-defined]
    except Exception:  # pragma: no cover
        try:
            from openapi_spec_validator import validate as _validate  # type: ignore[attr-defined]
        except Exception:  # very new API shapes
            from openapi_spec_validator.validators import validate as _validate  # type: ignore
    with open("docs/api/openapi.yaml", encoding="utf-8") as f:
        spec = yaml.safe_load(f)
    _validate(spec)  # type: ignore[arg-type]
