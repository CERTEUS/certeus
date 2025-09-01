#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/validate_policy_pack.py                     |

# | ROLE: Project module.                                       |

# | PLIK: scripts/validate_policy_pack.py                     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
from typing import Any

from jsonschema import Draft7Validator, Draft201909Validator, Draft202012Validator
import yaml  # type: ignore

# === KONFIGURACJA / CONFIGURATION ===
ENV_SCHEMA = "PCO_POLICY_PACK_SCHEMA"

ENV_PACK = "PCO_POLICY_PACK_PATH"

PII_FIELD_NAMES: set[str] = {
    "name",
    "first_name",
    "last_name",
    "pesel",
    "email",
    "phone",
    "address",
    "dob",
    "ssn",
    "patient_id",
    "person_id",
    "user_id",
}

ALLOWED_PUBLIC_FIELDS: set[str] = {
    "rid",
    "smt2_hash",
    "lfsc",
    "drat",
    "merkle_proof",
    "signature",
}

REQUIRED_PUBLIC_FIELDS: set[str] = {
    "rid",
    "smt2_hash",
    "lfsc",
    "merkle_proof",
    "signature",
}

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


DEFAULT_SCHEMA = Path("policies/pco/policy_pack.schema.v0.1.json")

DEFAULT_PACK = Path("policies/pco/policy_pack.v0.1.yaml")


ENDPOINT_PATTERN = re.compile(r"^/pco/public/\{case_id\}$")


# stdlib


# third-party

# ----Bloki----- STAŁE


# Denylista PII (klucze)


# Dozwolone klucze w publicznym payload


# Minimalny zestaw wymaganych pól


# ----Bloki----- I/O


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_yaml(path: Path) -> dict[str, Any]:
    data = yaml.safe_load(path.read_text(encoding="utf-8"))

    if not isinstance(data, dict):
        raise TypeError("YAML must decode to an object (mapping)")

    return data


# ----Bloki----- Dobór walidatora


def _pick_validator(schema: dict[str, Any]):
    ident = str(schema.get("$schema", "")).lower()

    if "draft-07" in ident:
        return Draft7Validator

    if "2019-09" in ident:
        return Draft201909Validator

    return Draft202012Validator


# ----Bloki----- Inwarianty


def _ensure_no_pii(fields: list[str], ctx: str, messages: list[dict[str, Any]]) -> None:
    lowered = {f.replace("?", "").lower() for f in fields}

    forbidden = sorted(lowered.intersection(PII_FIELD_NAMES))

    if forbidden:
        messages.append(
            {
                "level": "error",
                "code": "PII_FORBIDDEN",
                "where": ctx,
                "detail": f"PII fields not allowed: {', '.join(forbidden)}",
            }
        )


def _check_required_fields(fields: list[str], ctx: str, messages: list[dict[str, Any]]) -> None:
    s = set(x.replace("?", "") for x in fields)

    missing = sorted(REQUIRED_PUBLIC_FIELDS - s)

    if missing:
        messages.append(
            {
                "level": "error",
                "code": "REQUIRED_MISSING",
                "where": ctx,
                "detail": f"Missing required fields: {', '.join(missing)}",
            }
        )


def _check_unknown_fields(fields: list[str], ctx: str, messages: list[dict[str, Any]]) -> None:
    s = set(x.replace("?", "") for x in fields)

    unknown = sorted(s - ALLOWED_PUBLIC_FIELDS)

    if unknown:
        messages.append(
            {
                "level": "warning",
                "code": "UNKNOWN_FIELD",
                "where": ctx,
                "detail": f"Unknown fields present: {', '.join(unknown)}",
            }
        )


def _check_endpoint_pattern(endpoint: str, ctx: str, messages: list[dict[str, Any]]) -> None:
    if not ENDPOINT_PATTERN.fullmatch(endpoint):
        messages.append(
            {
                "level": "error",
                "code": "ENDPOINT_PATTERN",
                "where": ctx,
                "detail": f"Endpoint must match '^/pco/public/{{case_id}}$', got: {endpoint}",
            }
        )


def run_invariants(pack: dict[str, Any]) -> list[dict[str, Any]]:
    msgs: list[dict[str, Any]] = []

    use_cases = pack.get("use_cases", {})

    if not isinstance(use_cases, dict):
        msgs.append({"level": "error", "code": "USE_CASES_TYPE", "where": "use_cases", "detail": "must be object"})

        return msgs

    for uc_name, uc in use_cases.items():
        if not isinstance(uc, dict):
            msgs.append(
                {"level": "error", "code": "UC_TYPE", "where": f"use_cases.{uc_name}", "detail": "must be object"}
            )

            continue

        publish = uc.get("publish", {})

        if not isinstance(publish, dict):
            msgs.append(
                {
                    "level": "error",
                    "code": "PUBLISH_TYPE",
                    "where": f"use_cases.{uc_name}.publish",
                    "detail": "must be object",
                }
            )

            continue

        endpoint = str(publish.get("endpoint", ""))

        _check_endpoint_pattern(endpoint, f"use_cases.{uc_name}.publish.endpoint", msgs)

        fields = publish.get("fields", [])

        if not isinstance(fields, list) or not all(isinstance(x, str) for x in fields):
            msgs.append(
                {
                    "level": "error",
                    "code": "FIELDS_TYPE",
                    "where": f"use_cases.{uc_name}.publish.fields",
                    "detail": "must be array of strings",
                }
            )

            continue

        _ensure_no_pii(fields, f"use_cases.{uc_name}.publish.fields", msgs)

        _check_required_fields(fields, f"use_cases.{uc_name}.publish.fields", msgs)

        _check_unknown_fields(fields, f"use_cases.{uc_name}.publish.fields", msgs)

        # NEW: drat_required => wymagamy 'drat' w polach publikacji

        drat_required = bool(uc.get("drat_required", False))

        if drat_required and "drat" not in {f.replace("?", "") for f in fields}:
            msgs.append(
                {
                    "level": "error",
                    "code": "DRAT_REQUIRED",
                    "where": f"use_cases.{uc_name}.publish.fields",
                    "detail": "drat_required=true but 'drat' field not present",
                }
            )

    return msgs


# ----Bloki----- CLI


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="validate_policy_pack",
        description="Validate PCO Policy Pack (schema + invariants).",
    )

    p.add_argument("--schema", type=Path, default=Path(os.getenv(ENV_SCHEMA) or DEFAULT_SCHEMA))

    p.add_argument("--pack", type=Path, default=Path(os.getenv(ENV_PACK) or DEFAULT_PACK))

    p.add_argument("--format", choices=["text", "json"], default="text")

    p.add_argument("--strict", action="store_true")

    p.add_argument("--list-use-cases", action="store_true")

    return p.parse_args()


def _emit_text(schema_errors: list[str], messages: list[dict[str, Any]], use_cases: list[str]) -> None:
    if use_cases:
        print("[use_cases] " + ", ".join(use_cases))

    for e in schema_errors:
        print(f"[SCHEMA] {e}", file=sys.stderr)

    for m in messages:
        lvl = str(m.get("level", "info")).upper()

        code = str(m.get("code", "MSG"))

        where = str(m.get("where", "-"))

        detail = str(m.get("detail", ""))

        print(f"[{lvl}] {code} @ {where}: {detail}")


def _emit_json(schema_errors: list[str], messages: list[dict[str, Any]], use_cases: list[str]) -> None:
    out = {"use_cases": use_cases, "schema_errors": schema_errors, "messages": messages}

    print(json.dumps(out, ensure_ascii=False, indent=2))


# ----Bloki----- MAIN


def main() -> int:
    args = _parse_args()

    try:
        schema = _read_json(args.schema)

        pack = _read_yaml(args.pack)

    except Exception:
        return 4

    Validator = _pick_validator(schema)

    schema_errs = [
        f"{'/'.join(map(str, e.path))}: {e.message}"
        for e in sorted(Validator(schema).iter_errors(pack), key=lambda e: e.path)
    ]  # type: ignore[arg-type]

    messages = run_invariants(pack)

    uc_names: list[str] = []

    if args.list_use_cases and isinstance(pack.get("use_cases"), dict):
        uc_names = list(pack["use_cases"].keys())  # type: ignore[index]

    if args.format == "json":
        _emit_json(schema_errs, messages, uc_names)

    else:
        _emit_text(schema_errs, messages, uc_names)

    has_schema_errors = bool(schema_errs)

    has_errors = has_schema_errors or any(m.get("level") == "error" for m in messages)

    has_warnings = any(m.get("level") == "warning" for m in messages)

    if has_errors:
        return 2

    if has_warnings and args.strict:
        return 2

    if has_warnings:
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
