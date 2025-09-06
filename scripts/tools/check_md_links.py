#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/tools/check_md_links.py                      |
# | ROLE: Local docs link checker.                              |
# | PLIK: scripts/tools/check_md_links.py                      |
# | ROLA: Lokalny weryfikator linków w Markdown (docs/).        |
# +-------------------------------------------------------------+

"""
PL: Szybki walidator linków w plikach Markdown (docs/ i README.md).
    Sprawdza istnienie lokalnych ścieżek (pliki/asset-y). Ignoruje http(s) i kotwice (#...).

EN: Quick Markdown link checker for docs/ and README.md.
    Verifies local file targets exist. Ignores http(s) and anchors (#...).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import re
import sys

# === LOGIKA / LOGIC ===

LINK_PATTERN = re.compile(r"\[[^\]]+\]\(([^)]+)\)")


def iter_md_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for p in root.rglob("*.md"):
        # skip hidden and build output
        if any(part.startswith(".") for part in p.parts):
            continue
        files.append(p)
    # include top-level README.md if present
    top_readme = root.parent / "README.md"
    if top_readme.exists():
        files.append(top_readme)
    return files


def is_external_or_anchor(target: str) -> bool:
    t = target.strip()
    if not t or t.startswith("#"):
        return True
    return any(
        t.startswith(prefix) for prefix in ("http://", "https://", "mailto:", "tel:")
    )


def normalize_target(base: Path, target: str) -> Path:
    # strip anchors and query
    t = target.split("#", 1)[0].split("?", 1)[0]
    # mkdocs allows linking without leading ./
    candidate = (base.parent / t).resolve()
    return candidate


def check_links(md_root: Path) -> int:
    missing: list[str] = []
    for f in iter_md_files(md_root):
        text = f.read_text(encoding="utf-8", errors="ignore")
        for m in LINK_PATTERN.finditer(text):
            target = m.group(1).strip()
            if is_external_or_anchor(target):
                continue
            # tolerate links to .md without extension by trying .md
            cand = normalize_target(f, target)
            ok = cand.exists()
            if not ok:
                # try with .md appended
                cand_md = Path(str(cand) + ".md")
                if cand_md.exists():
                    ok = True
                else:
                    # try index.md for directory links
                    cand_index = cand / "index.md"
                    ok = cand_index.exists()
            if not ok:
                missing.append(f"{f}:{m.start(1) + 1} -> {target}")
    if missing:
        sys.stderr.write("Broken local links found (first 50):\n")
        for entry in missing[:50]:
            sys.stderr.write(f"- {entry}\n")
        return 1
    return 0


# === I/O / ENDPOINTS ===


def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    md_root = repo_root / "docs"
    return check_links(md_root)


if __name__ == "__main__":
    raise SystemExit(main())
