#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tools/fix_certeus_headers.py            |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

# -*- coding: utf-8 -*-
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  tools/fix_certeus_headers.py                                |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

"""
PL: Narzędzie do hurtowego wstrzykiwania banerów i docstringów w plikach
    wymaganych przez "CERTEUS header/docstring gate". Działa idempotentnie.
EN: Bulk injector of module banners and docstrings for the "CERTEUS
    header/docstring gate". Idempotent behavior.
"""

from __future__ import annotations
from pathlib import Path
import datetime
import re

# Uzupełniłem o brakujące dwa pliki:
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
    # Nowe:
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

DOCSTRING = '''"""
PL: {pl_desc}
EN: {en_desc}
"""
'''


def needs_banner(text: str) -> bool:
    return not text.lstrip().startswith(
        "# +====================================================================="
    )


def needs_docstring(text: str) -> bool:
    head = "\n".join(text.splitlines()[:25])
    return not re.search(r'^\s*("""|\'\'\')[\s\S]*?\1', head, re.M)


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
    today = datetime.date.today().isoformat()
    banner = BANNER.format(module_path=str(path).replace("\\", "/")[:60], today=today)

    new_text = text

    if needs_banner(text):
        shebang_block = ""
        rest = new_text
        if rest.startswith("#!"):
            nl = rest.find("\n")
            shebang_block, rest = rest[: nl + 1], rest[nl + 1 :]
        elif rest.startswith("# -*- coding:"):
            nl = rest.find("\n")
            shebang_block, rest = rest[: nl + 1], rest[nl + 1 :]
        new_text = f"{shebang_block}{banner}\n{rest}"
        updated = True

    if needs_docstring(new_text):
        pl, en = make_descriptions(path)
        doc = DOCSTRING.format(pl_desc=pl, en_desc=en).strip()
        parts = new_text.splitlines()
        insert_idx = 0
        if parts and parts[0].startswith("#!"):
            insert_idx = 1
        while insert_idx < len(parts) and parts[insert_idx].startswith("# "):
            insert_idx += 1
        parts.insert(insert_idx, doc)
        new_text = "\n".join(parts)
        if not new_text.endswith("\n"):
            new_text += "\n"
        updated = True

    if updated:
        path.write_text(new_text, encoding="utf-8")
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
