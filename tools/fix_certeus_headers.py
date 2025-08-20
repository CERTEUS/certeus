#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  tools/fix_certeus_headers.py                                |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

"""
PL: Hurtowy wstrzykiwacz banerów CERTEUS i docstringów modułów (idempotentny).
EN: Bulk injector for CERTEUS banners and module docstrings (idempotent).
"""

from __future__ import annotations

import datetime
import re
from pathlib import Path

# Lista naprawianych plików (z poprzednich runów gate’a)
FILES = [
    "services/api_gateway/app_e2e.py",
    "tests/services/test_mismatch_service.py",
    "services/api_gateway/routers/mismatch.py",
    "services/api_gateway/main.py",
    "services/exporter_service/exporter.py",
    "typings/z3/__init__.py",
    "kernel/e2e_verifier.py",
    "kernel/dual_core/__init__.py",
    "kernel/dual_core/z3_adapter.py",
    "services/ledger_service/ledger.py",
    "services/__init__.py",
    "tests/truth/test_smt_translator_ext.py",
    "tests/services/test_exporter_provenance.py",
    "kernel/truth_engine.py",
    "services/exporter_service/__init__.py",
    # dopełnienia:
    "tests/services/test_ledger.py",
    "tools/fix_certeus_headers.py",
]

BANNER = """# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  {module_path:<60}|
# | DATE:    {today:<60}|
# +=====================================================================+
"""

DOCSTRING_TMPL = '''"""
PL: {pl_desc}
EN: {en_desc}
"""
'''

# Bezpieczny wzorzec na docstring: potrójne " lub ' (symetryczne)
DOCSTRING_NEAR_TOP_RE = re.compile(r'(?ms)^\s*(["\'])\1\1(?P<body>.*?)(\1\1\1)\s*')


def needs_banner(text: str) -> bool:
    return not text.lstrip().startswith("# +=====================================================================")


def needs_docstring(text: str) -> bool:
    head = "\n".join(text.splitlines()[:25])
    return DOCSTRING_NEAR_TOP_RE.match(head) is None


def make_descriptions(p: Path) -> tuple[str, str]:
    name = str(p).replace("\\", "/")
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


def inject_header_and_docstring(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    updated = False

    # przygotuj baner
    today = datetime.date.today().isoformat()
    banner = BANNER.format(module_path=str(path).replace("\\", "/")[:60], today=today)

    new_text = text

    # shebang/encoding na górze – zachowaj
    lines = new_text.splitlines(keepends=True)
    i = 0
    if i < len(lines) and lines[i].startswith("#!"):
        i += 1
    if i < len(lines) and lines[i].startswith("# -*- coding:"):
        i += 1
    prefix = "".join(lines[:i])
    rest = "".join(lines[i:])

    # usuń WSZYSTKIE istniejące banery CERTEUS gdziekolwiek
    rest = re.sub(
        r"(?ms)^# \+={69}\+\n(?:# \|.*\n)+# \+={69}\+\n\n?",
        "",
        rest,
    )

    # dodaj nasz jeden kanoniczny pod shebangiem/encodingiem
    rest = banner + rest
    updated = True

    # docstring: zachowaj pierwszy jeśli jest na górze; jeśli nie ma – dodaj
    head = "\n".join(rest.splitlines()[:25])
    if DOCSTRING_NEAR_TOP_RE.match(head) is None:
        pl, en = make_descriptions(path)
        doc = DOCSTRING_TMPL.format(pl_desc=pl, en_desc=en).strip() + "\n\n"
        rest = doc + rest
        updated = True
    else:
        # jeśli po banerze jest WIĘCEJ niż jeden docstring PL/EN pod rząd – zredukuj do jednego
        parts = rest.splitlines(keepends=True)
        pos = 0
        # omiń baner (to 5–6 linii; wyłap marker linii granicznej)
        while pos < len(parts) and parts[pos].startswith("# "):
            pos += 1
        # od 'pos' – zredukuj ewentualne duplikaty docstringów PL/EN
        tail = "".join(parts[pos:])
        m = DOCSTRING_NEAR_TOP_RE.match(tail)
        if m:
            end = m.end()
            tail2 = tail[end:]
            # usuwaj kolejne docstringi PL/EN od razu po sobie
            while True:
                skip = re.match(r"(?ms)^(?:[ \t]*#.*\n|[ \t]*\n)*", tail2)
                s = skip.end() if skip else 0
                m2 = DOCSTRING_NEAR_TOP_RE.match(tail2[s:])
                if m2:
                    body = m2.group("body")
                    if "PL:" in body and "EN:" in body:
                        tail2 = tail2[:s] + tail2[s + m2.end() :]
                        updated = True
                        continue
                break
            rest = "".join(parts[:pos]) + tail[:end] + tail2

    if updated:
        path.write_text(prefix + rest, encoding="utf-8")
    return updated


def main() -> None:
    repo = Path(".").resolve()
    touched = []
    for rel in FILES:
        p = repo / rel
        if not p.exists() or not p.is_file():
            print(f"[skip] {rel} (missing)")
            continue
        if inject_header_and_docstring(p):
            print(f"[fix ] {rel}")
            touched.append(rel)
        else:
            print(f"[ok  ] {rel}")
    print(f"\nDone. Updated: {len(touched)} file(s).")


if __name__ == "__main__":
    main()
