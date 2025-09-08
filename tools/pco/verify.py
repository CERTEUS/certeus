#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# +-------------------------------------------------------------+
# | FILE: tools/pco/verify.py                                  |
# | ROLE: Validate PCO objects against JSON Schema v0.3        |
# +-------------------------------------------------------------+

import argparse
import json
from pathlib import Path
from typing import Any

try:
    from jsonschema import Draft202012Validator
except Exception:  # pragma: no cover - fallback for Windows CI invoking via `python3`
    # Attempt to locate local venv site-packages when invoked via a shim
    from pathlib import Path as _Path
    import sys as _sys

    # Repo root (three levels up from certeus/tools/pco)
    _root = _Path(__file__).resolve().parents[3]
    _cands = [
        _root / ".venv" / "Lib" / "site-packages",
        _root / "venv" / "Lib" / "site-packages",
    ]
    for _c in _cands:
        if _c.exists():
            _sys.path.insert(0, str(_c))
    from jsonschema import Draft202012Validator  # type: ignore  # noqa: E402


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def validate_pco(doc: dict[str, Any], schema: dict[str, Any]) -> None:
    validator = Draft202012Validator(schema)
    errors = sorted(validator.iter_errors(doc), key=lambda e: e.path)
    if errors:
        lines = [f"- {'/'.join(map(str, e.path)) or '<root>'}: {e.message}" for e in errors]
        raise SystemExit("PCO validation failed:\n" + "\n".join(lines))


def main() -> None:
    parser = argparse.ArgumentParser(description="Validate PCO using schema v0.3")
    parser.add_argument(
        "input",
        type=Path,
        help="Path to PCO JSON (e.g., certeus/examples/pco/hello.json)",
    )
    parser.add_argument(
        "--schema",
        type=Path,
        default=Path(__file__).resolve().parents[2] / "schemas" / "pco-v0.3.json",
        help="Path to schema JSON (default: repo schemas/pco-v0.3.json)",
    )
    args = parser.parse_args()

    doc = load_json(args.input)
    schema = load_json(args.schema)
    validate_pco(doc, schema)
    print("PCO: OK")


if __name__ == "__main__":
    main()
