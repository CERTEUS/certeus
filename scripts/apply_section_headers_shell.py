# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/apply_section_headers_shell.py              |

# | ROLE: Project module.                                       |

# | PLIK: scripts/apply_section_headers_shell.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

Dodaje znaczniki sekcji do plików Bash (.sh) i PowerShell (.ps1) zgodnie z sekcją 21.1.

Wstawiane po nagłówku/banerze: IMPORTY/CONFIG/LOGIKA/I-O/TESTY.

Idempotentne (nie dubluje jeśli już obecne).

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path

# === KONFIGURACJA / CONFIGURATION ===
SHELL_ROOTS = ["scripts"]

MARKERS = [
    "# === IMPORTY / IMPORTS ===\n",
    "# === KONFIGURACJA / CONFIGURATION ===\n",
    "# === LOGIKA / LOGIC ===\n",
    "# === I/O / ENDPOINTS ===\n",
    "# === TESTY / TESTS ===\n",
]

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def has_any_marker(text: str) -> bool:
    head = "\n".join(text.splitlines()[:120])

    return "# === " in head


def insert_after_banner(text: str) -> str | None:
    if has_any_marker(text):
        return None

    lines = text.splitlines(keepends=True)

    idx = 0

    # Skip shebang if present

    if lines and lines[0].startswith("#!/"):
        idx = 1

    # Skip banner block (lines starting with '#')

    while idx < len(lines) and (lines[idx].lstrip().startswith("#") or lines[idx].strip() == ""):
        idx += 1

    block = []

    block.extend(MARKERS)

    block.append("\n")

    new_text = "".join(lines[:idx] + block + lines[idx:])

    return new_text


def main() -> None:
    root = Path(__file__).resolve().parents[1]

    updated = 0

    for d in SHELL_ROOTS:
        base = root / d

        if not base.exists():
            continue

        for f in list(base.rglob("*.sh")) + list(base.rglob("*.ps1")):
            text = f.read_text(encoding="utf-8", errors="ignore")

            new_text = insert_after_banner(text)

            if new_text and new_text != text:
                f.write_text(new_text, encoding="utf-8")

                updated += 1

                print(f"[SECTIONS-SHELL] {f.relative_to(root)}")

    print(f"Done. Shell files updated: {updated}")


if __name__ == "__main__":
    main()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
