#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tools/normalize_certeus_headers.py                  |

# | ROLE: Project module.                                       |

# | PLIK: tools/normalize_certeus_headers.py                  |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/tools/normalize_certeus_headers.py      |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


"""

PL: Normalizator nagłówków CERTEUS i docstringów modułów.

    - Usuwa wszystkie istniejące banery CERTEUS w pliku i wstawia jeden kanoniczny

      pod shebangiem/encodingiem.

    - Gwarantuje jeden docstring modułu (zachowuje pierwszy; jeśli brak – dodaje PL/EN).

    - Działa idempotentnie; kolejne uruchomienia nie tworzą duplikatów.

    - Domyślnie zachowuje datę z pierwszego znalezionego banera, można wymusić dzisiejszą.



EN: CERTEUS header & module docstring normalizer.

    - Removes all existing CERTEUS banners and inserts a single canonical one

      below shebang/encoding.

    - Ensures a single module docstring (keeps first; if none, adds PL/EN).

    - Idempotent; subsequent runs don't duplicate.

    - Keeps the first banner's DATE by default; can force today's date.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

from __future__ import annotations

import argparse
from collections.abc import Iterable
import datetime
from pathlib import Path
import re

BORDER = "# +=====================================================================+"

CERTEUS_LINE = "# |                          CERTEUS                                    |"

MODULE_LABEL = "MODULE:"

DATE_LABEL = "DATE:"


CANONICAL_WIDTH = 60  # padding width inside "| ... |"


EXCLUDE_DIRS = {
    ".git",
    ".hg",
    ".svn",
    ".venv",
    "venv",
    "env",
    "__pycache__",
    "node_modules",
    "dist",
    "build",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".idea",
    ".vscode",
}


PY_GLOB = "**/*.py"


BANNER_RE = re.compile(rf"(?ms)^({re.escape(BORDER)}\n(?:# \|.*\n)+{re.escape(BORDER)}\n)")


DATE_LINE_RE = re.compile(r"# \|\s*DATE:\s*(?P<date>.*?)\s*\|")


TRIPLE_QUOTE_RE = re.compile(r'(?ms)^\s*(?P<q>"""|\'\'\')(?P<body>.*?)(?P=q)\s*')


def iter_py_files(root: Path) -> Iterable[Path]:
    for p in root.glob(PY_GLOB):
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue

        if p.is_file():
            yield p


def extract_banner_date(block: str) -> str | None:
    m = DATE_LINE_RE.search(block)

    if m:
        return m.group("date").strip()

    return None


def remove_all_banners(text: str) -> tuple[str, str | None]:
    """Remove all CERTEUS banner blocks. Return (text_wo_banners, first_date_if_any)."""

    first_date: str | None = None

    def repl(m: re.Match) -> str:
        nonlocal first_date

        block = m.group(1)

        if first_date is None:
            first_date = extract_banner_date(block)

        return ""  # drop this banner

    new_text = BANNER_RE.sub(repl, text)

    return new_text, first_date


def split_shebang_encoding(text: str) -> tuple[str, str]:
    """Return (prefix, rest) where prefix includes shebang/encoding lines."""

    lines = text.splitlines(keepends=True)

    idx = 0

    if idx < len(lines) and lines[idx].startswith("#!"):
        idx += 1

    if idx < len(lines) and lines[idx].startswith("# -*- coding:"):
        idx += 1

    return "".join(lines[:idx]), "".join(lines[idx:])


def build_banner(module_path: str, date_str: str) -> str:
    line_module = f"# | MODULE:  {module_path:<{CANONICAL_WIDTH}}|"

    line_date = f"# | DATE:    {date_str:<{CANONICAL_WIDTH}}|"

    return "\n".join([BORDER, CERTEUS_LINE, BORDER, line_module, line_date, BORDER]) + "\n\n"


def has_module_docstring_near_top(text_after_banner: str) -> tuple[bool, int, int]:
    """

    Detect a module-level docstring near file start (after comments).

    Returns (found, start_idx, end_idx) in char offsets in text_after_banner.

    """

    # Skip initial comment lines and blanks

    pos = 0

    while True:
        m = re.match(r"[ \t]*#.*\n", text_after_banner[pos:])

        if m:
            pos += m.end()

            continue

        m2 = re.match(r"[ \t]*\n", text_after_banner[pos:])

        if m2:
            pos += m2.end()

            continue

        break

    mdoc = TRIPLE_QUOTE_RE.match(text_after_banner[pos:])

    if mdoc:
        start = pos + mdoc.start()

        end = pos + mdoc.end()

        return True, start, end

    return False, -1, -1


def ensure_single_docstring(text_after_banner: str, module_path: str) -> str:
    """

    Keep the first module docstring (if present). Remove any additional PL/EN

    docstrings immediately following it. If none present, insert a generic PL/EN.

    """

    found, start, end = has_module_docstring_near_top(text_after_banner)

    if found:
        # Remove any additional docstrings appearing right after the first (duplicates).

        tail = text_after_banner[end:]

        # Repeatedly strip PL/EN style docstrings at the very top of 'tail'

        while True:
            # skip blanks/comments

            skip = re.match(r"(?ms)^(?:[ \t]*#.*\n|[ \t]*\n)*", tail)

            s = skip.end() if skip else 0

            next_doc = TRIPLE_QUOTE_RE.match(tail[s:])

            if next_doc:
                body = next_doc.group("body")

                if "PL:" in body and "EN:" in body:
                    tail = tail[:s] + tail[s + next_doc.end() :]

                    continue

            break

        return text_after_banner[:end] + tail

    # No docstring → insert canonical PL/EN

    pl_desc, en_desc = make_descriptions(module_path)

    doc = f'"""\nPL: {pl_desc}\nEN: {en_desc}\n"""\n\n'

    return doc + text_after_banner


def make_descriptions(module_path: str) -> tuple[str, str]:
    name = module_path

    if "tests/" in name:
        return (
            "Testy jednostkowe / integracyjne modułu.",
            "Module test suite (unit/integration).",
        )

    if "routers/" in name:
        return (
            "Router FastAPI dla usług CERTEUS.",
            "FastAPI router for CERTEUS services.",
        )

    if name.endswith("__init__.py"):
        return ("Pakiet inicjalizacyjny modułu.", "Package initializer.")

    if "ledger" in name:
        return ("Księga pochodzenia (ledger) – logika.", "Provenance ledger – logic.")

    if "exporter" in name:
        return ("Eksport raportów i artefaktów procesu.", "Report/artefact exporter.")

    if "smt_translator" in name:
        return (
            "Translator SMT i powiązana logika.",
            "SMT translator and related logic.",
        )

    if "e2e_verifier" in name:
        return (
            "Weryfikator E2E przepływów CERTEUS.",
            "E2E verifier for CERTEUS flows.",
        )

    if "z3_adapter" in name:
        return ("Adapter dla Z3 i zależności SMT.", "Adapter for Z3 and SMT.")

    return ("Moduł systemu CERTEUS.", "CERTEUS system module.")


def normalize_file(p: Path, set_date_today: bool, dry_run: bool) -> bool:
    """

    Returns True if file was modified.

    """

    text = p.read_text(encoding="utf-8")

    # 1) Remove all existing banners (capture first DATE)

    text_wo_banners, first_date = remove_all_banners(text)

    # 2) Split out shebang/encoding

    prefix, rest = split_shebang_encoding(text_wo_banners)

    # 3) Insert canonical banner

    module_path = str(p).replace("\\", "/")

    date_str = (
        datetime.date.today().isoformat() if set_date_today else (first_date or datetime.date.today().isoformat())
    )

    banner = build_banner(module_path, date_str)

    # If rest already starts with the same banner, avoid duplication

    if rest.startswith(banner):
        new_rest = rest

    else:
        new_rest = banner + rest

    # 4) Ensure exactly one module docstring

    new_rest = ensure_single_docstring(new_rest, module_path)

    new_text = prefix + new_rest

    if new_text != text:
        if not dry_run:
            p.write_text(new_text, encoding="utf-8")

        return True

    return False


def main() -> None:
    ap = argparse.ArgumentParser(description="Normalize CERTEUS banners and module docstrings across repository.")

    ap.add_argument("--root", default=".", help="Repository root (default: .)")

    ap.add_argument(
        "--set-date",
        choices=["today", "keep"],
        default="keep",
        help="Use today's date for banner DATE or keep existing (default: keep).",
    )

    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Only report changes, do not write files.",
    )

    args = ap.parse_args()

    root = Path(args.root).resolve()

    set_date_today = args.set_date == "today"

    changed = 0

    total = 0

    for py in iter_py_files(root):
        total += 1

        if normalize_file(py, set_date_today=set_date_today, dry_run=args.dry_run):
            print(f"[fix ] {py}")

            changed += 1

        else:
            # print(f"[ok  ] {py}")

            pass

    print(f"\nDone. Scanned: {total} file(s), updated: {changed} file(s).")


if __name__ == "__main__":
    main()
