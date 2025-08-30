# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/scripts/lexlog_eval_smoke.py            |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |               CERTEUS - LEXLOG Smoke Evaluator              |
# +-------------------------------------------------------------+
# | PLIK: lexlog_eval_smoke.py                                  |
# | ROLA: Szybki test spełnienia art. 286 k.k. na podstawie     |
# |       reguł z kk.lex i mapowania kk.mapping.json.          |
# +-------------------------------------------------------------+
#
# PL: Jeśli nie podasz pliku z flagami (--flags), skrypt użyje
#     domyślnych trzech ról faktów, wymaganych przez art. 286:
#       - intent_financial_gain
#       - act_deception
#       - detrimental_property_disposal
#
# EN: If you don’t pass a flags file (--flags), the script uses
#     the default three fact roles required by Art. 286:
#       - intent_financial_gain
#       - act_deception
#       - detrimental_property_disposal
"""
PL: Smoke-test Jądra Prawdy: wczytuje flags JSON i sprawdza spełnialność.
EN: Truth Engine smoke test: loads flags JSON and checks satisfiability.
"""

from __future__ import annotations

import argparse
from collections.abc import Mapping
import json
from pathlib import Path

from services.lexlog_parser.evaluator import evaluate_rule
from services.lexlog_parser.mapping import load_mapping
from services.lexlog_parser.parser import parse_lexlog

RULE_ID = "R_286_OSZUSTWO"
RULES_PATH = Path("packs/jurisdictions/PL/rules/kk.lex")
MAP_PATH = Path("packs/jurisdictions/PL/rules/kk.mapping.json")

DEFAULT_FLAGS: Mapping[str, bool] = {
    "intent_financial_gain": True,
    "act_deception": True,
    "detrimental_property_disposal": True,
}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--flags", type=str, default="", help="Ścieżka do pliku JSON z kluczem 'flags'")
    args = ap.parse_args()

    if not RULES_PATH.exists():
        raise SystemExit(f"[FATAL] Missing rules file: {RULES_PATH}")
    if not MAP_PATH.exists():
        raise SystemExit(f"[FATAL] Missing mapping file: {MAP_PATH}")

    ast = parse_lexlog(RULES_PATH.read_text(encoding="utf-8"))
    ctx = load_mapping(MAP_PATH)

    if args.flags:
        flags_path = Path(args.flags)
        if not flags_path.exists():
            raise SystemExit(f"[ERROR] Missing flags file: {flags_path}")
        data = json.loads(flags_path.read_text(encoding="utf-8"))
        flags = data.get("flags", {})
    else:
        flags = dict(DEFAULT_FLAGS)

    # Now evaluate explicit rule id (4-arg signature).
    res = evaluate_rule(ast, RULE_ID, flags, ctx)

    if getattr(res, "satisfied", False):
        print("[SUCCESS] art. 286 satisfied")
    else:
        missing = getattr(res, "missing_premises", []) or []
        failing = getattr(res, "failing_excludes", []) or []
        print("[ERROR] art. 286 NOT satisfied")
        if missing:
            print("  missing_premises:", sorted(missing))
        if failing:
            print("  failing_excludes:", sorted(failing))


if __name__ == "__main__":
    main()
