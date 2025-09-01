"""
Remove legacy CERTEUS banner blocks in Python files.

Legacy pattern: a contiguous comment block that contains a line of
"# +=====================================================================+"
and mentions "CERTEUS" and "MODULE"/"DATE". We remove that entire comment
block while keeping the new standard banner (which uses dashes).

PL: Usuwa stary baner CERTEUS (z linią '='). Nowy standard ma linie z '-'.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path

# === KONFIGURACJA / CONFIGURATION ===
ROOTS = [
    "cje",
    "clients",
    "core",
    "kernel",
    "plugins",
    "scripts",
    "services",
    "tests",
]

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def strip_legacy_block(text: str) -> tuple[str, bool]:
    lines = text.splitlines(keepends=True)
    n = len(lines)
    changed = False
    # search for legacy header start anywhere in first ~200 lines
    start = -1
    for idx in range(min(n, 200)):
        if lines[idx].lstrip().startswith("# +================"):
            start = idx
            break
    if start == -1:
        return text, False

    # Determine the extent of contiguous comment block to remove
    end = start
    while end < n and (lines[end].lstrip().startswith("#") or lines[end].strip() == ""):
        # Heuristic: stop if we encounter the first non-comment after banner
        end += 1

    # Remove only if block mentions CERTEUS and MODULE/DATE
    block = "".join(lines[start:end]).lower()
    if "certeus" in block and ("module" in block or "date" in block):
        # Delete the block
        del lines[start:end]
        changed = True
    return "".join(lines), changed


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    total = 0
    for d in ROOTS:
        p = root / d
        if not p.exists():
            continue
        for f in p.rglob("*.py"):
            text = f.read_text(encoding="utf-8", errors="ignore")
            new, changed = strip_legacy_block(text)
            if changed:
                f.write_text(new, encoding="utf-8")
                total += 1
                print(f"[CLEANED] {f.relative_to(root)}")
    print(f"Done. Legacy headers removed: {total}")


if __name__ == "__main__":
    main()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
