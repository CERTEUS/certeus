"""
Add CERTEUS headers to HTML and JS files under clients/.

PL: Dodaje nagłówek CERTEUS do plików HTML/JS w clients/.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def has_header(text: str, kind: str) -> bool:
    head = "\n".join(text.splitlines()[:10]).lower()
    if kind == "html":
        return "certeus" in head and "file:" in head
    return "certeus" in head and "file:" in head


def build_html_header(rel: str) -> str:
    return (
        "<!--\n"
        "+-------------------------------------------------------------+\n"
        "|                          CERTEUS                            |\n"
        "+-------------------------------------------------------------+\n"
        f"| FILE: {rel:<52}|\n"
        "| ROLE: Web client page.                                      |\n"
        f"| PLIK: {rel:<52}|\n"
        "| ROLA: Strona klienta web.                                   |\n"
        "+-------------------------------------------------------------+\n"
        "-->\n"
    )


def build_js_header(rel: str) -> str:
    return (
        "/*\n"
        "+-------------------------------------------------------------+\n"
        "|                          CERTEUS                            |\n"
        "+-------------------------------------------------------------+\n"
        f"| FILE: {rel:<52}|\n"
        "| ROLE: Web client script.                                     |\n"
        f"| PLIK: {rel:<52}|\n"
        "| ROLA: Skrypt klienta web.                                    |\n"
        "+-------------------------------------------------------------+\n"
        "*/\n"
    )


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    base = root / "clients"
    if not base.exists():
        print("No clients/ directory; skipping")
        return
    total = 0
    for f in base.rglob("*.html"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        if not has_header(text, "html"):
            rel = str(f.relative_to(root)).replace("\\", "/")
            f.write_text(build_html_header(rel) + "\n" + text, encoding="utf-8")
            print(f"[UPDATED] {rel}")
            total += 1
    for f in base.rglob("*.js"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        if not has_header(text, "js"):
            rel = str(f.relative_to(root)).replace("\\", "/")
            f.write_text(build_js_header(rel) + "\n" + text, encoding="utf-8")
            print(f"[UPDATED] {rel}")
            total += 1
    print(f"Done. Web files updated: {total}")


if __name__ == "__main__":
    main()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
