# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/normalize_py_headers.py                     |

# | ROLE: Project module.                                       |

# | PLIK: scripts/normalize_py_headers.py                     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+



"""

Ujednolica kolejność nagłówków w plikach Python zgodnie z sekcją 21:

shebang/encoding → baner CERTEUS → module docstring (PL/EN) → reszta.



EN: Normalize Python file headers: shebang/encoding → CERTEUS banner →

module docstring (PL/EN) → rest of the code.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import ast

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























def detect_shebang_and_encoding(lines: list[str]) -> tuple[int, int]:

    """Return indices for shebang line and encoding cookie (0 or -1 if missing)."""

    shebang = 0 if lines and lines[0].startswith("#!") else -1

    enc = -1

    # PEP 263: encoding cookie must be in first or second line

    for i in range(0, min(len(lines), 2)):

        if "coding:" in lines[i] or "coding=" in lines[i]:

            enc = i

            break

    return shebang, enc





def find_banner_block(lines: list[str]) -> tuple[int, int] | None:

    """Find CERTEUS banner block: start,end (inclusive-exclusive)."""

    # search in first ~60 lines

    limit = min(len(lines), 60)

    start = -1

    for i in range(limit):

        if lines[i].lstrip().startswith("# +----------------"):

            # look ahead few lines for CERTEUS and FILE:

            head = "".join(lines[i : min(i + 15, limit)]).lower()

            if "certeus" in head and "file:" in head:

                start = i

                break

    if start == -1:

        return None

    j = start

    while j < len(lines) and (lines[j].lstrip().startswith("#") or lines[j].strip() == ""):

        j += 1

    return (start, j)





def extract_docstring_block(text: str) -> tuple[tuple[int, int] | None, str | None]:

    """Return (start,end) line indices (inclusive) and docstring content (raw)."""

    try:

        mod = ast.parse(text)

    except Exception:

        return None, None

    if not mod.body:

        return None, None

    node = mod.body[0]

    if (

        not isinstance(node, ast.Expr)

        or not isinstance(getattr(node, "value", None), ast.Constant)

        or not isinstance(node.value.value, str)

    ):

        return None, None

    # ast lines are 1-based, inclusive

    start = node.lineno - 1

    end = getattr(node, "end_lineno", node.lineno) - 1

    # raw content

    ds = ast.get_docstring(mod)

    return (start, end), ds





def build_default_docstring(rel: str) -> str:

    return (

        '"""\n'

        f"PL: Moduł {rel} — uzupełnij opis funkcjonalny.\n\n"

        f"EN: Module {rel} — please complete the functional description.\n"

        '"""\n'

    )





def main() -> None:

    root = Path(__file__).resolve().parents[1]

    changed = 0

    for d in ROOTS:

        p = root / d

        if not p.exists():

            continue

        for f in p.rglob("*.py"):

            text = f.read_text(encoding="utf-8", errors="ignore")

            lines = text.splitlines(keepends=True)

            if not lines:

                continue

            sb_idx, enc_idx = detect_shebang_and_encoding(lines)

            # header_top not needed; compute positions directly

            banner = find_banner_block(lines)

            ds_span, ds_content = extract_docstring_block(text)



            # Need at least banner or docstring to reorder

            if not banner and not ds_span:

                continue



            # Build new ordering explicitly; do not reuse sliced parts



            # Extract banner chunk

            if banner:

                b_start, b_end = banner

                banner_part = lines[b_start:b_end]

            else:

                # No banner — skip (we assume banner already inserted by apply_headers)

                banner_part = []



            # Extract docstring chunk

            if ds_span:

                ds_start, ds_end = ds_span

                doc_part = lines[ds_start : ds_end + 1]

                if not ds_content:

                    # Ensure non-empty

                    doc_part = [build_default_docstring(str(f.relative_to(root)).replace("\\", "/"))]

            else:

                doc_part = [build_default_docstring(str(f.relative_to(root)).replace("\\", "/"))]



            # Remove original banner/docstring occurrences

            to_remove = set()

            if banner:

                to_remove.update(range(banner[0], banner[1]))

            if ds_span:

                to_remove.update(range(ds_span[0], ds_span[1] + 1))



            body = [ln for idx, ln in enumerate(lines) if idx not in to_remove]



            # Determine insertion index after shebang/encoding

            insert_idx = 0

            if sb_idx == 0:

                insert_idx = 1

            if enc_idx != -1 and enc_idx + 1 > insert_idx:

                insert_idx = enc_idx + 1



            # Ensure blank line separation

            core_header = []

            if banner_part:

                core_header.extend(banner_part)

            if core_header and (not core_header[-1].endswith("\n")):

                core_header[-1] = core_header[-1] + "\n"

            # Add blank line between banner and docstring

            if core_header and (len(core_header) == 0 or core_header[-1].strip() != ""):

                core_header.append("\n")

            # Docstring

            core_header.extend(doc_part if isinstance(doc_part, list) else [doc_part])

            if core_header and core_header[-1].strip() != "":

                core_header.append("\n")



            # Reassemble

            new_lines = []

            # keep shebang/encoding part as in original

            if sb_idx == 0:

                new_lines.append(lines[0])

            if enc_idx != -1:

                # If encoding is not on line 1, preserve original line

                new_lines.append(lines[enc_idx])



            # Insert header

            new_lines.extend(core_header)



            # Append remaining body (skipping duplicate shebang/encoding if they were elsewhere)

            for i, ln in enumerate(body):

                if i == 0 and sb_idx == 0:

                    # first element of body might be encoding if shebang removed earlier; we already added

                    pass

                new_lines.append(ln)



            new_text = "".join(new_lines)

            if new_text != text:

                f.write_text(new_text, encoding="utf-8")

                changed += 1

                print(f"[NORMALIZED] {f.relative_to(root)}")

    print(f"Done. Python files normalized: {changed}")





if __name__ == "__main__":

    main()









# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

