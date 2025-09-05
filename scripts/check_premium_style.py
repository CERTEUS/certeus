# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/check_premium_style.py                      |

# | ROLE: Project module.                                       |

# | PLIK: scripts/check_premium_style.py                      |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

CI Gate: Premium Code Style (sec. 21)

Sprawdza repo wg kluczowych punktów z sekcji 21:

- Python: baner CERTEUS + module docstring (PL/EN) + obecność sekcji (# === ... ===)

- YAML/HTML/JS/SH/PS1: nagłówek (baner) z FILE/PLIK i CERTEUS

Zwraca kod 0 (OK) lub 1 (naruszenia). Wypisuje listę problemów.

"""

from __future__ import annotations

import ast
from pathlib import Path
import sys

REPO = Path(__file__).resolve().parents[1]

# Exact top-level directories to skip
SKIP_DIRS = {
    ".git",
    ".github/ci-status",  # status branch checkout (when present)
    "node_modules",
    "dist",
    "build",
    "__pycache__",
    ".ruff_cache",
    ".pytest_cache",
    "clients/web/public/brand",
    "out",
    "reports",
}

# Prefix-based directories to skip anywhere in tree (handles local/CI venvs)
SKIP_DIR_PREFIXES = (
    ".venv",
    "venv",
    "_venv",
    "mirror_",
)

def _should_skip(rel: str) -> bool:
    # Normalize to POSIX-style
    r = rel.replace("\\", "/")
    # Skip exact directories at repo root
    if any(r == d or r.startswith(d + "/") for d in SKIP_DIRS):
        return True
    # Skip any path containing virtualenv or mirrors
    parts = r.split("/")
    for part in parts:
        if any(part.startswith(pfx) for pfx in SKIP_DIR_PREFIXES):
            return True
    # Skip third-party packages laid out in local/CI envs
    if "/site-packages/" in r or r.endswith("/site-packages") or "/dist-packages/" in r:
        return True
    return False

def iter_files(patterns: list[str]) -> list[Path]:
    out: list[Path] = []
    for p in REPO.rglob("*"):
        try:
            rel = p.relative_to(REPO).as_posix()
        except Exception:
            continue
        # Skip vendor/venv before stat (avoid bad symlinks on Windows)
        if _should_skip(rel):
            continue
        try:
            if not p.is_file():
                continue
        except OSError:
            continue
        if any(rel.endswith(suf) for suf in patterns):
            out.append(p)
    return out

def has_banner_head(text: str) -> bool:
    head = "\n".join(text.splitlines()[:80]).lower()
    return ("certeus" in head) and ("file:" in head)

def has_sections_head(text: str) -> bool:
    head = "\n".join(text.splitlines()[:200])

    return "# === " in head

def has_module_docstring(text: str) -> bool:
    try:
        tree = ast.parse(text)
        return ast.get_docstring(tree) is not None
    except Exception:
        # Do not block gate on docstring if parse fails (banner/sections remain enforced)
        return True

def check_python() -> list[str]:
    errs: list[str] = []

    for f in iter_files([".py"]):
        t = f.read_text(encoding="utf-8", errors="ignore")

        if not has_banner_head(t):
            errs.append(f"[PY][BANNER] {f.relative_to(REPO)}")

        if not has_module_docstring(t):
            errs.append(f"[PY][DOCSTRING] {f.relative_to(REPO)}")

        if not has_sections_head(t):
            errs.append(f"[PY][SECTIONS] {f.relative_to(REPO)}")

        # Detect decorators that are not immediately followed (skipping blank/comment
        # lines) by another decorator, a class or a function definition. This guards
        # against accidental insertion of section markers between a decorator and
        # its target (class/def), which breaks Python syntax.
        lines = t.splitlines()
        n = len(lines)
        orphan_found = False
        for i in range(n):
            s = lines[i].lstrip()
            if not s.startswith("@"):  # decorator candidate
                continue
            j = i + 1
            while j < n and (lines[j].strip() == "" or lines[j].lstrip().startswith("#")):
                # If we hit a section header between decorator and target → orphan
                if lines[j].lstrip().startswith("# === "):
                    orphan_found = True
                    break
                j += 1
            if orphan_found:
                break
            if j >= n:
                orphan_found = True
                break
            nxt = lines[j].lstrip()
            if not (
                nxt.startswith("@")
                or nxt.startswith("def ")
                or nxt.startswith("async def ")
                or nxt.startswith("class ")
            ):
                orphan_found = True
                break
        if orphan_found:
            rel = f.relative_to(REPO).as_posix()
            if not rel.startswith("tests/"):
                errs.append(f"[PY][DECORATOR_ORDER] {rel}")

    return errs

def check_textual(exts: list[str], label: str) -> list[str]:
    errs: list[str] = []

    for f in iter_files(exts):
        t = f.read_text(encoding="utf-8", errors="ignore")

        if not has_banner_head(t):
            errs.append(f"[{label}][BANNER] {f.relative_to(REPO)}")

    return errs

def main() -> int:
    issues: list[str] = []

    issues += check_python()

    issues += check_textual([".yaml", ".yml"], "YAML")

    issues += check_textual([".html"], "HTML")

    issues += check_textual([".js"], "JS")

    issues += check_textual([".sh"], "SH")

    issues += check_textual([".ps1"], "PS1")

    if issues:
        print("Premium Code Style violations (sec.21):", file=sys.stderr)

        for line in issues:
            print(line, file=sys.stderr)

        return 1

    print("Premium Code Style: OK")

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
