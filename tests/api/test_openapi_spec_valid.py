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

from openapi_spec_validator import validate_spec
import yaml

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===


def test_openapi_spec_is_valid() -> None:
    with open("docs/api/openapi.yaml", encoding="utf-8") as f:
        spec = yaml.safe_load(f)
    validate_spec(spec)  # type: ignore[arg-type]
