# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/scripts/generate_proofs.py              |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/generate_proofs.py                            |
# | ROLE: CLI to generate stub/simulated proofs to an output dir|
# | PLIK: scripts/generate_proofs.py                            |
# | ROLA: CLI generujące atrapy/symulacje dowodów do katalogu.  |
# +-------------------------------------------------------------+
"""
PL: Skrypt CLI generujący pliki dowodów (tryb 'stub' / 'simulate') do wskazanego katalogu.
EN: CLI script that produces proof files (stub/simulate modes) into a chosen output directory.
"""

from __future__ import annotations

import argparse
import random
import string
from pathlib import Path
from typing import Final, Iterable, List, Optional


# === MAPOWANIA / MAPPINGS ===================================== #

# format -> nazwa pliku
FORMAT_TO_FILE: Final[dict[str, str]] = {
    "drat": "z3.drat",
    "lfsc": "cvc5.lfsc",
}

# format -> nazwa „solvera” (do treści pliku)
FORMAT_TO_SOLVER: Final[dict[str, str]] = {
    "drat": "z3",
    "lfsc": "cvc5",
}


# === POMOCNICZE / HELPERS ===================================== #


def _lazy_console():
    """
    Leniwy import utils.console (działa także z uruchomienia w osobnym procesie).
    """
    try:
        from utils.console import info, success, error  # type: ignore

        return info, success, error
    except ModuleNotFoundError:
        import sys

        root = Path(__file__).resolve().parents[1]
        if str(root) not in sys.path:
            sys.path.insert(0, str(root))
        from utils.console import info, success, error  # type: ignore

        return info, success, error


def _rand_token(n: int = 24) -> str:
    alphabet = string.ascii_letters + string.digits
    return "".join(random.choices(alphabet, k=n))


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    # ASCII-safe/UTF-8, LF line endings
    path.write_text(content, encoding="utf-8", newline="\n")


def _normalize_formats(formats: Optional[List[str]]) -> list[str]:
    if not formats:
        return list(FORMAT_TO_FILE.keys())
    out: list[str] = []
    for f in formats:
        lf = f.lower()
        if lf in FORMAT_TO_FILE:
            out.append(lf)
    return out


# === API / PUBLIC ============================================= #


def generate_proofs(
    out: Path, formats: Optional[List[str]] = None, mode: str = "simulate"
) -> list[Path]:
    """
    PL: Generuje pliki proof w `out` dla zadanych `formats` i trybu `mode`.
        - formats: podzbiór z {"drat", "lfsc"}; None => oba.
        - mode: "simulate" (zawartość z losowym nonce) lub "stub" (prosty stub).
    EN: Generate proof files in `out` for given `formats` and `mode`.
        - formats: subset of {"drat", "lfsc"}; None => both.
        - mode: "simulate" (content with random nonce) or "stub" (simple stub).
    Returns: list of created file paths.
    """
    log_info, log_success, log_error = _lazy_console()

    fs = _normalize_formats(formats)
    if not fs:
        log_error("No valid formats provided.")
        return []

    created: list[Path] = []

    for fmt in fs:
        solver = FORMAT_TO_SOLVER[fmt]
        fname = FORMAT_TO_FILE[fmt]
        dst = out / fname

        if mode == "simulate":
            payload = f"PROOF::format={fmt}::solver={solver}::nonce={_rand_token(24)}"
            _write_text(dst, payload)
            # ważne: test oczekuje tej frazy:
            log_success(f"Created simulated proof with content: {dst}")
        elif mode == "stub":
            payload = f"PROOF-STUB::format={fmt}::solver={solver}"
            _write_text(dst, payload)
            log_success(f"Created stub proof: {dst}")
        else:
            log_error(f"Unknown mode: {mode}")
            return []

        created.append(dst)

    log_info(f"Total proofs: {len(created)}")
    return created


# === CLI ======================================================= #


def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="generate_proofs",
        description="Generate (simulated) proofs into an output directory.",
    )
    p.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output directory for generated proof files.",
    )
    p.add_argument(
        "--mode",
        choices=["simulate", "stub"],
        default="simulate",
        help="Generation mode (default: simulate).",
    )
    p.add_argument(
        "--formats",
        nargs="*",
        choices=sorted(FORMAT_TO_FILE.keys()),
        default=None,
        help="Formats to generate (space separated), e.g. --formats drat lfsc. Default: both.",
    )
    return p


def main(argv: Iterable[str] | None = None) -> int:
    log_info, _log_success, log_error = _lazy_console()

    parser = _build_arg_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)

    try:
        files = generate_proofs(args.out, formats=args.formats, mode=args.mode)
    except Exception as exc:  # pragma: no cover
        log_error(f"Generation failed: {exc}")
        return 1

    # pokaż co zapisaliśmy (INFO w stdout)
    for p in files:
        log_info(f"Wrote: {p}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
