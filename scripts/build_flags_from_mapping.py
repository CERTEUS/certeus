# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/build_flags_from_mapping.py                 |

# | ROLE: Project module.                                       |

# | PLIK: scripts/build_flags_from_mapping.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Buduje plik flags JSON na podstawie mapowania przesłanek→flagi silnika.

    Uzupełnia brakujące przesłanki przez mapę P_* → ZNAMIE_* (MVP).

EN: Builds flags JSON from mapping of premises→engine flags. Fills missing

    premises via P_* → ZNAMIE_* mapping (MVP).

"""

from __future__ import annotations

import argparse
from collections.abc import Iterable as AbcIterable, Mapping, MutableMapping, Sequence
from inspect import Signature, signature
import json
from pathlib import Path
import re
from typing import (
    Any,
    cast,
)

from services.lexlog_parser.evaluator import evaluate_rule
from services.lexlog_parser.mapping import load_mapping
from services.lexlog_parser.parser import parse_lexlog


def _to_set(xs: object | None) -> set[str]:
    """

    PL: Zamiana dowolnego wejścia na set[str] z jawnie typowanym elementem.

    EN: Convert arbitrary input to set[str] with explicit element typing.

    """

    out: set[str] = set()

    if xs is None:
        return out

    if isinstance(xs, str):
        out.add(xs)

        return out

    if isinstance(xs, AbcIterable) and not isinstance(xs, bytes | bytearray):
        for elem in cast(AbcIterable[object], xs):
            s: str = str(elem)

            out.add(s)

        return out

    out.add(str(xs))

    return out


def _detect_rule_id_from_text(text: str, prefer_token: str = "286") -> str | None:
    """

    PL: Wyszukaj identyfikatory po 'RULE' i preferuj ten zawierający token (np. '286').

    EN: Extract identifiers after 'RULE' and prefer one containing a token (e.g. '286').

    """

    ids = re.findall(r"^\s*RULE\s+([A-Za-z0-9_.\-]+)", text, flags=re.MULTILINE)

    if not ids:
        return None

    for rid in ids:
        if prefer_token and prefer_token.lower() in rid.lower():
            return rid

    return ids[0]


def _call_evaluate(ast: Any, rule_id: str | None, flags: Mapping[str, bool], ctx: Any) -> Any:
    """

    PL: Wywołaj evaluate_rule zgodnie z aktualną sygnaturą (różne wersje).

    EN: Call evaluate_rule according to the current signature (versions may differ).

    """

    sig: Signature = signature(evaluate_rule)

    params: Sequence[str] = list(sig.parameters.keys())

    kwargs: dict[str, Any] = {}

    if "ast" in params:
        kwargs["ast"] = ast

    if "rule_id" in params:
        if not rule_id:
            raise ValueError("evaluate_rule requires 'rule_id' but none was detected")

        kwargs["rule_id"] = rule_id

    if "flags" in params:
        kwargs["flags"] = flags

    if "ctx" in params:
        kwargs["ctx"] = ctx

    try:
        return evaluate_rule(**kwargs)  # type: ignore[misc]

    except TypeError:
        # Fallbacks for very old signatures

        try:
            if "rule_id" not in params:
                return evaluate_rule(ast, flags, ctx)  # type: ignore[misc]

        except TypeError:
            return evaluate_rule(ast, flags)  # type: ignore[misc]


def _step(
    ast: Any, rule_id: str | None, flags: MutableMapping[str, bool], ctx: Any
) -> tuple[bool, set[str], set[str], Any]:
    """

    PL: Jeden krok ewaluacji -> (ok, missing_premises, failing_excludes, raw_result).

    EN: One evaluation step -> (ok, missing_premises, failing_excludes, raw_result).

    """

    res = _call_evaluate(ast, rule_id, flags, ctx)

    ok = bool(getattr(res, "satisfied", False))

    missing = _to_set(getattr(res, "missing_premises", []) or [])

    failing = _to_set(getattr(res, "failing_excludes", []) or [])

    return ok, missing, failing, res


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="build_flags_from_mapping",
        description="Build flags JSON by iteratively satisfying a rule.",
    )

    parser.add_argument(
        "--rules",
        default="packs/jurisdictions/PL/rules/kk.lex",
        help="Path to .lex file",
    )

    parser.add_argument(
        "--map",
        default="packs/jurisdictions/PL/rules/kk.mapping.json",
        help="Path to mapping.json",
    )

    parser.add_argument(
        "--out",
        default="packs/jurisdictions/PL/flags/lexenith_results_latest.json",
        help="Output JSON file",
    )

    parser.add_argument("--rule-id", default=None, help="Explicit rule_id (overrides auto-detection)")

    parser.add_argument(
        "--prefer-token",
        default="286",
        help="Token preferred when auto-selecting RULE id",
    )

    parser.add_argument("--max-iter", type=int, default=10, help="Max refinement iterations")

    args = parser.parse_args()

    rules_path = Path(args.rules)

    map_path = Path(args.map)

    out_path = Path(args.out)

    rules_text = rules_path.read_text(encoding="utf-8")

    ast = parse_lexlog(rules_text)

    ctx = load_mapping(map_path)

    rule_id = args.rule_id or _detect_rule_id_from_text(rules_text, prefer_token=args.prefer_token)

    if rule_id:
        print(f"[INFO] Using rule_id: {rule_id}")

    else:
        print("[WARN] Could not detect rule_id from .lex; trying evaluator without rule_id")

    flags: dict[str, bool] = {}

    for _ in range(args.max_iter):
        ok, miss, fail, _ = _step(ast, rule_id, flags, ctx)

        if ok:
            break

        if miss:
            for p in miss:
                engine_flag = ctx.premise_to_flag.get(p)  # P_* -> ZNAMIE_* jeśli dostępne

                key = str(engine_flag or p)

                flags[key] = True

        if fail:
            for k in fail:
                flags[str(k)] = False

    out_path.parent.mkdir(parents=True, exist_ok=True)

    out_path.write_text(json.dumps({"flags": flags}, ensure_ascii=True, indent=2), encoding="utf-8")

    print("[OK] wrote", out_path)

    print("[OK] True:", sorted([k for k, v in flags.items() if v]))

    print("[OK] False:", sorted([k for k, v in flags.items() if not v]))


if __name__ == "__main__":
    main()
