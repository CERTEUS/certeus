# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/validate_schemas.py                         |

# | ROLE: Project module.                                       |

# | PLIK: scripts/validate_schemas.py                         |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Ten moduł zapewnia, że wszystkie kontrakty danych (schematy) są

    zgodne ze standardem JSON Schema Draft 7 oraz spełniają minimalne

    wymogi jakości (title/description, spójność required/properties).



EN: Ensures all data contracts (schemas) comply with JSON Schema Draft 7

    and pass minimal quality gates (title/description presence,

    required/properties consistency).

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json

from pathlib import Path

from typing import Any

from jsonschema import Draft7Validator  # Only what we truly use

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===
















SCHEMA_DIR = Path("schemas")


def _check_quality(name: str, schema: dict[str, Any]) -> list[str]:
    """

    PL: Dodatkowe bramki jakości dla schematów.

    EN: Additional quality gates for schemas.

    """

    errs: list[str] = []

    # Wymagamy tytułu i opisu

    if not schema.get("title"):
        errs.append("Missing 'title'")

    if not schema.get("description"):
        errs.append("Missing 'description'")

    # Spójność required/properties na poziomie root

    props = schema.get("properties", {})

    required = schema.get("required", [])

    for key in required:
        if key not in props:
            errs.append(f"'required' contains '{key}' not present in 'properties'")

    # Restrykcyjność: preferujemy additionalProperties:false na root

    if schema.get("additionalProperties", True) is not False:
        errs.append("Root 'additionalProperties' should be false for stricter contracts")

    return errs


def main() -> None:
    """

    PL: Główna funkcja — weryfikuje syntaksę schematów i bramki jakości.

    EN: Main routine — verifies schema syntax and quality gates.

    """

    print(f"🔎 Validating schemas in: {SCHEMA_DIR.absolute()}")

    has_errors = False

    schema_files = sorted(SCHEMA_DIR.glob("*.json"))

    if not schema_files:
        print("⚠️ No schemas found to validate.")

        raise SystemExit(0)

    for schema_path in schema_files:
        print(f"--- Checking: {schema_path.name} ---")

        try:
            schema_instance = json.loads(schema_path.read_text(encoding="utf-8"))

        except json.JSONDecodeError as e:
            print(f"❌ ERROR: Invalid JSON in {schema_path.name}: {e}")

            has_errors = True

            continue

        # Walidacja składniowa samego schematu

        try:
            Draft7Validator.check_schema(schema_instance)

            print("✅ Schema syntax is valid.")

        except Exception as e:  # noqa: BLE001
            print(f"❌ ERROR: Schema is invalid in {schema_path.name}: {e}")

            has_errors = True

            continue

        # Bramka jakości

        q_errs = _check_quality(schema_path.name, schema_instance)

        if q_errs:
            has_errors = True

            for q in q_errs:
                print(f"❌ QUALITY: {q}")

        else:
            print("✨ Quality gate passed.")

    if has_errors:
        print("\n💥 Validation failed for one or more schemas.")

        raise SystemExit(1)

    print("\n🎉 All schemas are syntactically valid and passed quality checks!")


if __name__ == "__main__":
    main()





# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

