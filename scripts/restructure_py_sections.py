# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/restructure_py_sections.py                  |

# | ROLE: Project module.                                       |

# | PLIK: scripts/restructure_py_sections.py                  |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

Przenosi bloki kodu do sekcji (sec. 21.1) w wybranych modułach Python

w sposób zachowujący semantykę:

- importy → IMPORTY

- stałe/konfiguracja (UPPER_CASE) → KONFIGURACJA

- klasy modeli (BaseModel) → MODELE

- endpointy FastAPI (@router.*) → I/O / ENDPOINTS

- reszta → LOGIKA

Zakres domyślny: core/pco/** oraz services/api_gateway/routers/**.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import ast
from pathlib import Path

# === KONFIGURACJA / CONFIGURATION ===

ROOTS = [
    ("core", True),
    ("services", True),
    ("kernel", True),
    ("plugins", True),
    ("clients", True),
    ("scripts", True),
]

MARKERS = [
    "# === IMPORTY / IMPORTS ===\n",
    "# === KONFIGURACJA / CONFIGURATION ===\n",
    "# === MODELE / MODELS ===\n",
    "# === LOGIKA / LOGIC ===\n",
    "# === I/O / ENDPOINTS ===\n",
    "# === TESTY / TESTS ===\n",
]

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def get_span(node: ast.AST) -> tuple[int, int]:
    # Include decorators for FunctionDef so we don't leave orphan decorator lines

    start_lineno = getattr(node, "lineno", 1)

    if isinstance(node, ast.FunctionDef) and node.decorator_list:
        first_dec = min(getattr(d, "lineno", start_lineno) for d in node.decorator_list)

        start_lineno = min(start_lineno, first_dec)

    end_lineno = getattr(node, "end_lineno", getattr(node, "lineno", 1))

    return (start_lineno - 1, end_lineno - 1)


def is_enum_class(node: ast.ClassDef) -> bool:
    enum_bases = {"Enum", "IntEnum", "StrEnum"}

    for b in node.bases:
        if isinstance(b, ast.Name) and b.id in enum_bases:
            return True

        if isinstance(b, ast.Attribute) and b.attr in enum_bases:
            return True

    return False


def is_model_class(node: ast.ClassDef) -> bool:
    # Traktuj wszystkie klasy jako modele (deklaracje) by były przed logiką/konfiguracją

    return True


def _is_simple_literal(value: ast.AST) -> bool:
    """Return True for literals/containers only (no Calls/Names), safe for CONFIG."""

    if isinstance(value, ast.Constant):
        return True

    if isinstance(value, ast.Dict | ast.List | ast.Tuple | ast.Set):
        # ensure children are simple as well

        for child in ast.walk(value):
            if isinstance(child, ast.Call | ast.Lambda | ast.Name | ast.Attribute):
                return False

        return True

    return False


def is_upper_name_target(node: ast.AST) -> bool:
    targets: list[str] = []

    if isinstance(node, ast.Assign):
        for t in node.targets:
            if isinstance(t, ast.Name):
                targets.append(t.id)

        value = node.value

    elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
        targets.append(node.target.id)

        value = node.value

    else:
        return False

    # Must be UPPER_CASE and simple literal (avoid moving initializations depending on classes)

    return any(name.isupper() for name in targets) and _is_simple_literal(value)


def is_endpoint_func(node: ast.FunctionDef) -> bool:
    for dec in node.decorator_list:
        # @router.get("/...") or @router.post ...

        try:
            expr = dec.func if isinstance(dec, ast.Call) else dec

            if isinstance(expr, ast.Attribute) and isinstance(expr.value, ast.Name) and expr.value.id == "router":
                return True

            if (
                isinstance(expr, ast.Attribute)
                and isinstance(expr.value, ast.Attribute)
                and getattr(expr.value, "attr", "") == "router"
            ):
                return True

        except Exception:
            continue

    return False


def has_markers(text: str) -> bool:
    head = "\n".join(text.splitlines()[:200])

    return "# === IMPORTY / IMPORTS ===" in head


def rebuild(text: str, rel: str) -> str | None:
    if not has_markers(text):
        return None

    try:
        mod = ast.parse(text)

    except Exception:
        return None

    lines = text.splitlines(keepends=True)

    n = len(lines)

    # Identify header (banner + docstring)

    # Assume docstring is first statement

    doc_start = 0

    doc_end = -1

    if mod.body:
        node0 = mod.body[0]

        if (
            isinstance(node0, ast.Expr)
            and isinstance(getattr(node0, "value", None), ast.Constant)
            and isinstance(node0.value.value, str)
        ):
            doc_start, doc_end = get_span(node0)

    header_end = doc_end

    if header_end < 0:
        # place header end at top

        header_end = 0

    covered: set[int] = set()

    imports_spans: list[tuple[int, int]] = []

    config_spans: list[tuple[int, int]] = []

    model_spans: list[tuple[int, int, int]] = []  # (priority, start, end)

    endpoint_spans: list[tuple[int, int]] = []

    for node in mod.body:
        s, e = get_span(node)

        if isinstance(node, ast.Import) or isinstance(node, ast.ImportFrom):
            imports_spans.append((s, e))

        elif (isinstance(node, ast.Assign) or isinstance(node, ast.AnnAssign)) and is_upper_name_target(node):
            config_spans.append((s, e))

        elif isinstance(node, ast.ClassDef) and is_model_class(node):
            prio = 0 if is_enum_class(node) else 1

            model_spans.append((prio, s, e))

        elif isinstance(node, ast.FunctionDef) and is_endpoint_func(node):
            endpoint_spans.append((s, e))

    def pick_blocks(spans: list[tuple[int, int]]) -> list[str]:
        out: list[str] = []

        for s, e in spans:
            if s <= header_end:
                # skip header/docstring area

                continue

            for i in range(s, e + 1):
                covered.add(i)

            out.extend(lines[s : e + 1])

            if not out or not out[-1].endswith("\n"):
                out.append("\n")

            if out and out[-1].strip() != "":
                out.append("\n")

        return out

    imports_block = pick_blocks(imports_spans)

    config_block = pick_blocks(config_spans)

    # models: sort by (priority, source order)

    models_block = []

    for _, s, e in sorted(model_spans, key=lambda x: (x[0], x[1])):
        models_block.extend(pick_blocks([(s, e)]))

    endpoints_block = pick_blocks(endpoint_spans)

    # Remaining logic: lines after header not covered and not marker lines

    logic_block: list[str] = []

    for i in range(header_end + 1, n):
        if i in covered:
            continue

        ln = lines[i]

        if ln.startswith("# === "):
            continue

        logic_block.append(ln)

    # Compose new text with standard markers order

    header_part = lines[: header_end + 1]

    out_lines: list[str] = []

    out_lines.extend(header_part)

    if not (out_lines and out_lines[-1].strip() == ""):
        out_lines.append("\n")

    def add_section(title: str, block: list[str]) -> None:
        out_lines.append(title)

        if block:
            out_lines.extend(block)

        else:
            out_lines.append("\n")

    add_section(MARKERS[0], imports_block)

    add_section(MARKERS[1], config_block)

    add_section(MARKERS[2], models_block)

    add_section(MARKERS[3], logic_block)

    add_section(MARKERS[4], endpoints_block)

    add_section(MARKERS[5], [])  # keep placeholder for tests

    new_text = "".join(out_lines)

    if new_text != text:
        return new_text

    return None


def main() -> None:
    root = Path(__file__).resolve().parents[1]

    changed = 0

    for d, _ in ROOTS:
        base = root / d

        if not base.exists():
            continue

        for f in base.rglob("*.py"):
            text = f.read_text(encoding="utf-8", errors="ignore")

            new_text = rebuild(text, str(f.relative_to(root)))

            if new_text:
                f.write_text(new_text, encoding="utf-8")

                changed += 1

                print(f"[RESTRUCTURED] {f.relative_to(root)}")

    print(f"Done. Files restructured: {changed}")


if __name__ == "__main__":
    main()

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
