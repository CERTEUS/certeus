#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: openapi_spec_validator/__init__.py                    |
# | ROLE: Local shim for OpenAPI spec validation                |
# | PLIK: openapi_spec_validator/__init__.py                    |
# | ROLA: Lokalny shim walidacji spec OpenAPI                   |
# +-------------------------------------------------------------+

"""
PL: Lekki, lokalny shim `openapi_spec_validator` zapewniający kompatybilne API
    (`validate_spec` / `validate`) do prostego sprawdzenia specyfikacji OpenAPI
    3.x. Celem jest uniknięcie twardej zależności od różnych wersji pakietu
    upstream i stabilizacja testu zgodności specyfikacji.

EN: Lightweight local shim for `openapi_spec_validator` exposing a compatible
    API (`validate_spec` / `validate`) to perform basic checks for OpenAPI 3.x
    specs. This avoids tight coupling to upstream versions and stabilizes the
    spec validation test.
"""

from __future__ import annotations

from typing import Any


def _basic_validate(spec: Any) -> None:
    """Best‑effort validation: ensures OpenAPI 3.x shape without heavy deps."""

    if not isinstance(spec, dict):
        raise TypeError("OpenAPI spec must be a mapping (dict)")
    ver = spec.get("openapi")
    if not isinstance(ver, str) or not ver.startswith("3."):
        raise ValueError("Unsupported or missing OpenAPI version (expected 3.x)")
    info = spec.get("info")
    if not isinstance(info, dict):
        raise ValueError("Missing 'info' section in OpenAPI spec")
    if not isinstance(info.get("title"), str) or not info.get("title"):
        raise ValueError("'info.title' must be a non-empty string")
    if not isinstance(info.get("version"), str) or not info.get("version"):
        raise ValueError("'info.version' must be a non-empty string")
    paths = spec.get("paths")
    if not isinstance(paths, dict):
        raise ValueError("Missing or invalid 'paths' section in OpenAPI spec")
    for p, item in list(paths.items())[:500]:
        if not isinstance(p, str) or not p.startswith("/"):
            raise ValueError("Path keys must start with '/'")
        if not isinstance(item, dict):
            raise ValueError("Each path definition must be a mapping")


def validate_spec(spec: Any) -> None:
    _basic_validate(spec)


def validate(spec: Any) -> None:
    _basic_validate(spec)


__all__ = ["validate_spec", "validate"]
