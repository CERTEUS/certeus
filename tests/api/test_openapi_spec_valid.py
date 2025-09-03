from __future__ import annotations

from openapi_spec_validator import validate_spec
import yaml


def test_openapi_spec_is_valid() -> None:
    with open("docs/api/openapi.yaml", "r", encoding="utf-8") as f:
        spec = yaml.safe_load(f)
    # Will raise on invalid spec
    validate_spec(spec)  # type: ignore[arg-type]

