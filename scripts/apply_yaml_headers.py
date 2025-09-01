"""
Add a lightweight CERTEUS header to YAML files that miss one.

PL: Dodaje lekki nagłówek (komentarze) na górze plików YAML.
"""

from __future__ import annotations

from pathlib import Path

ROOTS = [
    "infra",
    "charts",
    "policies",
    "plugins",
    "docs",
]


def has_header(text: str) -> bool:
    head = "\n".join(text.splitlines()[:10]).lower()
    return "certeus" in head and "file:" in head


def build_header(rel: str) -> str:
    return (
        "# +-------------------------------------------------------------+\n"
        "# |                          CERTEUS                            |\n"
        "# +-------------------------------------------------------------+\n"
        f"# | FILE: {rel:<52}|\n"
        "# | ROLE: Project YAML manifest.                                |\n"
        f"# | PLIK: {rel:<52}|\n"
        "# | ROLA: Manifest YAML projektu.                               |\n"
        "# +-------------------------------------------------------------+\n"
    )


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    total = 0
    for d in ROOTS:
        p = root / d
        if not p.exists():
            continue
        for f in p.rglob("*.y*ml"):
            text = f.read_text(encoding="utf-8", errors="ignore")
            if has_header(text):
                continue
            rel = str(f.relative_to(root)).replace("\\", "/")
            new_text = build_header(rel) + "\n" + text
            f.write_text(new_text, encoding="utf-8")
            total += 1
            print(f"[UPDATED] {rel}")
    print(f"Done. YAML files updated: {total}")


if __name__ == "__main__":
    main()

