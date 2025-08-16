# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/generate_proofs.py                            |
# | ROLE: Project module.                                       |
# | PLIK: scripts/generate_proofs.py                            |
# | ROLA: ModuĹ‚ projektu.                                       |
# +-------------------------------------------------------------+

# +-------------------------------------------------------------+
# |                    CERTEUS - Proof Generator                |
# |       Core Engine for Reliable & Unified Systems            |
# +-------------------------------------------------------------+
# | FILE / PLIK: generate_proofs.py                             |
# | ROLE / ROLA:                                                |
# |   EN: Generates proof artifacts (DRAT/LFSC) with support    |
# |       for format selection, stub/simulated modes,           |
# |       colored logs, and CI/CD-friendly exit codes.          |
# |   PL: Generuje artefakty dowodowe (DRAT/LFSC) z obsĹ‚ugÄ…     |
# |       wyboru formatu, trybu stub/symulacji, kolorowych logĂłw|
# |       oraz kodĂłw wyjĹ›cia zgodnych z CI/CD.                  |
# +-------------------------------------------------------------+

"""
PL:
    Ten moduĹ‚ odpowiada za generowanie artefaktĂłw dowodowych w formatach DRAT (Z3) i LFSC (CVC5).
    ObsĹ‚uguje dwa tryby dziaĹ‚ania:
        - 'stub'      â†’ tworzy puste pliki (placeholdery)
        - 'simulate'  â†’ generuje przykĹ‚adowÄ… zawartoĹ›Ä‡ (symulacja solvera)
    ModuĹ‚ jest kompatybilny z pipeline'ami CI/CD i uĹĽywa kolorowych logĂłw.

EN:
    This module is responsible for generating proof artifacts in DRAT (Z3) and LFSC (CVC5) formats.
    It supports two modes of operation:
        - 'stub'      â†’ creates empty files (placeholders)
        - 'simulate'  â†’ generates sample content (solver simulation)
    The module is CI/CD-friendly and uses colored logs.
"""

# [BLOCK: IMPORTS]
from __future__ import annotations
import argparse
import hashlib
import sys
import time
from pathlib import Path
from typing import List


# === Helper logging functions / Funkcje pomocnicze do logowania ===
def log_info(msg: str) -> None:
    """EN: Print informational message. | PL: WyĹ›wietla komunikat informacyjny."""
    print(f"\033[94m[INFO]\033[0m {msg}")


def log_success(msg: str) -> None:
    """EN: Print success message. | PL: WyĹ›wietla komunikat o powodzeniu."""
    print(f"\033[92m[SUCCESS]\033[0m {msg}")


def log_error(msg: str) -> None:
    """EN: Print error message. | PL: WyĹ›wietla komunikat o bĹ‚Ä™dzie."""
    print(f"\033[91m[ERROR]\033[0m {msg}")


# === Simulated proof generation / Symulowane generowanie dowodu ===
def simulate_solver_content(format_name: str) -> str:
    """
    EN: Generates simulated proof content for demonstration purposes.
    PL: Generuje symulowanÄ… treĹ›Ä‡ dowodu na potrzeby demonstracji.
    """
    timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
    header = (
        f"# Proof generated in simulated mode\n"
        f"# Format: {format_name.upper()}\n"
        f"# Timestamp: {timestamp}\n"
    )
    body = "c This is a simulated proof artifact.\np cnf 3 2\n1 -3 0\n2 3 -1 0\n"
    return header + body


# === SHA256 sidecar writer / Zapis plikĂłw *.sha256 ===
def write_sha256(file_path: Path) -> None:
    """
    EN: Writes a sidecar '<name>.sha256' file with '<digest>  <filename>'.
    PL: Zapisuje plik towarzyszÄ…cy '<nazwa>.sha256' z '<suma>  <plik>'.
    """
    digest = hashlib.sha256(file_path.read_bytes()).hexdigest()
    (file_path.with_suffix(file_path.suffix + ".sha256")).write_text(
        f"{digest}  {file_path.name}\n",
        encoding="utf-8",
    )
    log_info(f"SHA256 written: {file_path.name} â†’ {digest}")


# === Core proof generation logic / GĹ‚Ăłwna logika generowania dowodĂłw ===
def generate_proofs(out_dir: Path, formats: List[str], mode: str) -> None:
    """
    EN: Generates proof files in the specified formats and mode.
    PL: Generuje pliki dowodowe w okreĹ›lonych formatach i trybie.
    """
    start_time = time.time()
    try:
        # Ensure output directory exists / Upewnij siÄ™, ĹĽe katalog wyjĹ›ciowy istnieje
        out_dir.mkdir(parents=True, exist_ok=True)
        if not out_dir.is_dir():
            raise ValueError(f"Path {out_dir} is not a directory.")

        for fmt in formats:
            # Select file name based on format / WybĂłr nazwy pliku na podstawie formatu
            file_path = out_dir / (f"z3.{fmt}" if fmt == "drat" else f"cvc5.{fmt}")

            if mode == "stub":
                # Pusty placeholder jest OK (hash = e3b0...); alternatywnie moĹĽesz wstawiÄ‡ krĂłtki podpis.
                file_path.touch(exist_ok=True)
                log_success(f"Created empty stub proof: {file_path}")
            elif mode == "simulate":
                file_path.write_text(simulate_solver_content(fmt), encoding="utf-8")
                log_success(f"Created simulated proof with content: {file_path}")
            else:
                raise ValueError(f"Unknown mode: {mode}")

            # NEW: zapis pliku *.sha256 dla kaĹĽdego artefaktu
            write_sha256(file_path)

        elapsed = round(time.time() - start_time, 2)
        log_info(f"Proof generation completed in {elapsed} seconds.")
    except Exception as e:
        log_error(str(e))
        sys.exit(1)  # CI/CD failure code


# === CLI Interface / Interfejs wiersza poleceĹ„ ===
def main() -> None:
    """
    EN: Command-line entry point for proof generation.
    PL: Punkt wejĹ›cia z wiersza poleceĹ„ dla generowania dowodĂłw.
    """
    parser = argparse.ArgumentParser(
        description=(
            "EN: Generate proof artifacts in DRAT/LFSC formats.\n"
            "PL: Generuj artefakty dowodowe w formatach DRAT/LFSC."
        )
    )
    parser.add_argument(
        "--out",
        type=str,
        required=True,
        help="EN: Output directory for proofs. | PL: Katalog wyjĹ›ciowy dla dowodĂłw.",
    )
    parser.add_argument(
        "--formats",
        nargs="+",
        choices=["drat", "lfsc"],
        default=["drat", "lfsc"],
        help=(
            "EN: Formats to generate (default: both). "
            "| PL: Format(y) do wygenerowania (domyĹ›lnie: oba)."
        ),
    )
    parser.add_argument(
        "--mode",
        choices=["stub", "simulate"],
        default="stub",
        help=(
            "EN: Generation mode: 'stub' for empty files, 'simulate' for example content. "
            "| PL: Tryb generowania: 'stub' dla pustych plikĂłw, 'simulate' dla przykĹ‚adowej treĹ›ci."
        ),
    )
    args = parser.parse_args()
    generate_proofs(Path(args.out), args.formats, args.mode)


# === Script execution guard / Blok uruchomienia skryptu ===
if __name__ == "__main__":
    main()
