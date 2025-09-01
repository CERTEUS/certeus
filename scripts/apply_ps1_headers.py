"""
Dodaje baner CERTEUS do plików PowerShell (.ps1), jeśli brakuje.

EN: Add CERTEUS banner to PowerShell scripts when missing.
"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

from __future__ import annotations

from pathlib import Path

ROOTS = ["scripts"]


def has_header(text: str) -> bool:
    head = "\n".join(text.splitlines()[:10]).lower()
    return "certeus" in head and "file:" in head


def build_header(rel: str) -> str:
    return (
        "# +-------------------------------------------------------------+\n"
        "# |                          CERTEUS                            |\n"
        "# +-------------------------------------------------------------+\n"
        f"# | FILE: {rel:<52}|\n"
        "# | ROLE: PowerShell script.                                    |\n"
        f"# | PLIK: {rel:<52}|\n"
        "# | ROLA: Skrypt PowerShell.                                     |\n"
        "# +-------------------------------------------------------------+\n"
    )


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    total = 0
    for d in ROOTS:
        p = root / d
        if not p.exists():
            continue
        for f in p.rglob("*.ps1"):
            text = f.read_text(encoding="utf-8", errors="ignore")
            if has_header(text):
                continue
            rel = str(f.relative_to(root)).replace("\\", "/")
            new_text = build_header(rel) + "\n" + text
            f.write_text(new_text, encoding="utf-8")
            print(f"[UPDATED] {rel}")
            total += 1
    print(f"Done. PS1 files updated: {total}")


if __name__ == "__main__":
    main()
