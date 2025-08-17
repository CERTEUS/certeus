# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | FILE / PLIK: scripts/generate_proofs.py                             |
# | ROLE / ROLA:                                                         |
# |   EN: CLI to generate simulated/stub proof artifacts for Proof Gate |
# |   PL: CLI do generowania symulowanych/stubowych artefaktów dowodów  |
# | DATE: 2025-08-17                                                    |
# +=====================================================================+

"""
PL:
  Skrypt CLI generujący pliki dowodów do katalogu wyjściowego (parametr --out).
  Obsługuje tryby:
    - "simulate"  -> plik z treścią zawierającą losowy nonce (dla realizmu),
    - "stub"      -> minimalny stub bez nonce.
  Obsługiwane formaty:
    - "drat"  -> z3.drat
    - "lfsc"  -> cvc5.lfsc
  Dodatkowo może tworzyć pliki wejściowe:
    - input.smt2 (SMT-LIB),
    - input.cnf  (DIMACS),
  oraz opcjonalnie wygenerować pokwitowanie (receipt) z hashami SHA-256.

EN:
  CLI script that produces proof files into the given output directory (--out).
  Modes:
    - "simulate" -> file content includes a random nonce (more realistic),
    - "stub"     -> minimal stub content, no nonce.
  Supported formats:
    - "drat"  -> z3.drat
    - "lfsc"  -> cvc5.lfsc
  It can also emit input files:
    - input.smt2 (SMT-LIB),
    - input.cnf  (DIMACS),
  and optionally write a receipt (manifest) with SHA-256 hashes.
"""

from __future__ import annotations

# === IMPORTS =================================================== #
import argparse
import hashlib
import json
import os
import random
import string
import sys
from collections.abc import Iterable
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Final

# === CONSTANTS / KONSTANTY ===================================== #

FORMAT_TO_FILE: Final[dict[str, str]] = {
    "drat": "z3.drat",
    "lfsc": "cvc5.lfsc",
}

FORMAT_TO_SOLVER: Final[dict[str, str]] = {
    "drat": "z3",
    "lfsc": "cvc5",
}

SMT2_FILE: Final[str] = "input.smt2"
CNF_FILE: Final[str] = "input.cnf"
RECEIPT_FILE: Final[str] = "provenance_receipt_v1.json"


# === LOGGING (PL/EN) =========================================== #


def _lazy_console():
    """
    PL: Próbujemy użyć utils.console (Twój projekt). W razie braku – fallback na print.
    EN: Try to import project's utils.console; fall back to print-based logger if missing.
    """
    try:
        from utils.console import error, info, success  # type: ignore

        return info, success, error
    except Exception:

        def _info(msg: str) -> None:
            print(f"[INFO] {msg}")

        def _success(msg: str) -> None:
            print(f"[OK]   {msg}")

        def _error(msg: str) -> None:
            print(f"[ERR]  {msg}", file=sys.stderr)

        return _info, _success, _error


# === HELPERS / POMOCNICZE ===================================== #


def _write_text(path: Path, content: str) -> None:
    """
    PL: Zapisuje tekst UTF-8 z LF; tworzy katalogi pośrednie.
    EN: Writes UTF-8 text with LF; creates parent dirs.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8", newline="\n")


def _write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "wb") as f:
        f.write(data)


def _sha256_hex(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def _rand_token(n: int = 24) -> str:
    alphabet = string.ascii_letters + string.digits
    return "".join(random.choices(alphabet, k=n))


def _normalize_formats(formats: list[str] | None) -> list[str]:
    if not formats:
        return list(FORMAT_TO_FILE.keys())
    out: list[str] = []
    for f in formats:
        lf = f.lower()
        if lf in FORMAT_TO_FILE:
            out.append(lf)
    return out


# === DATA / DANE =============================================== #


@dataclass
class Generated:
    """
    PL: Informacja o wygenerowanym pliku.
    EN: Info about a generated file.
    """

    kind: str  # "proof" | "input" | "receipt"
    format: str | None  # "drat"/"lfsc" for proofs, None for others
    path: Path
    sha256: str


# === CORE / LOGIKA ============================================= #


def _emit_proof_file(fmt: str, out_dir: Path, mode: str, seed: int | None) -> Path:
    """
    PL: Tworzy plik dowodu w zadanym formacie i trybie.
    EN: Creates a proof file for the given format and mode.
    """
    if seed is not None:
        random.seed(seed)

    solver = FORMAT_TO_SOLVER[fmt]
    fname = FORMAT_TO_FILE[fmt]
    dst = out_dir / fname

    if mode == "simulate":
        # UWAGA: poniższy komunikat "Created simulated proof with content:"
        # jest istotny dla istniejących testów E2E.
        payload = f"PROOF::format={fmt}::solver={solver}::nonce={_rand_token(24)}"
        _write_text(dst, payload)
    elif mode == "stub":
        payload = f"PROOF-STUB::format={fmt}::solver={solver}"
        _write_text(dst, payload)
    else:
        raise ValueError(f"Unknown mode: {mode}")

    return dst


def _emit_inputs(out_dir: Path, smt2: bool, cnf: bool) -> list[Path]:
    """
    PL: Opcjonalnie generuje pliki wejściowe SMT2 / CNF.
    EN: Optionally generates SMT2 / CNF input files.
    """
    created: list[Path] = []

    if smt2:
        smt_path = out_dir / SMT2_FILE
        smt_content = "\n".join(
            [
                "(set-logic ALL)",
                "(set-info :source |CERTEUS simulated SMT2 input|)",
                "(assert true)",
                "(check-sat)",
                "(exit)",
            ]
        )
        _write_text(smt_path, smt_content)
        created.append(smt_path)

    if cnf:
        cnf_path = out_dir / CNF_FILE
        # Minimal, valid DIMACS header; no clauses.
        _write_text(cnf_path, "p cnf 1 0\n")
        created.append(cnf_path)

    return created


def _emit_receipt(out_dir: Path, items: list[Generated]) -> Path:
    """
    PL: Zapisuje pokwitowanie (provenance receipt) z hashami i timestampem.
    EN: Writes a provenance receipt with hashes and timestamp.
    """
    now = datetime.now(timezone.utc).isoformat()
    manifest = {
        "version": "provenance_receipt_v1",
        "created_at": now,
        "artifacts": [
            {
                "kind": it.kind,
                "format": it.format,
                "path": str(Path(os.path.relpath(it.path, out_dir)).as_posix()),
                "sha256": it.sha256,
            }
            for it in items
        ],
    }
    dst = out_dir / RECEIPT_FILE
    _write_text(dst, json.dumps(manifest, ensure_ascii=False, indent=2))
    return dst


def generate_proofs(
    out: Path,
    formats: list[str] | None = None,
    mode: str = "simulate",
    with_inputs: bool = False,
    seed: int | None = None,
    write_receipt: bool = False,
) -> list[Path]:
    """
    PL:
      Generuje pliki dowodów w katalogu `out`. Zwraca listę utworzonych ścieżek.
      - formats: podzbiór {"drat","lfsc"}; None => oba.
      - mode: "simulate" | "stub"
      - with_inputs: czy tworzyć input.smt2 i input.cnf
      - seed: ustala ziarno losowości (deterministyczny nonce w simulate)
      - write_receipt: czy zapisać manifest z hashami (provenance_receipt_v1.json)

    EN:
      Generates proof files in `out`. Returns list of created paths.
      - formats: subset {"drat","lfsc"}; None => both.
      - mode: "simulate" | "stub"
      - with_inputs: whether to create input.smt2 and input.cnf
      - seed: seed for reproducible nonce in simulate mode
      - write_receipt: write a manifest with SHA-256 hashes
    """
    log_info, log_success, log_error = _lazy_console()

    fs = _normalize_formats(formats)
    if not fs:
        log_error("No valid formats provided.")
        return []

    out.mkdir(parents=True, exist_ok=True)

    created: list[Generated] = []

    # Proofs
    for fmt in fs:
        dst = _emit_proof_file(fmt, out, mode, seed)
        sha = _sha256_hex(dst)
        created.append(Generated(kind="proof", format=fmt, path=dst, sha256=sha))

        if mode == "simulate":
            # Ten log jest celowy (używany przez testy):
            log_success(f"Created simulated proof with content: {dst}")
        else:
            log_success(f"Created stub proof: {dst}")

    # Inputs
    if with_inputs:
        for ip in _emit_inputs(out, smt2=True, cnf=True):
            created.append(Generated(kind="input", format=None, path=ip, sha256=_sha256_hex(ip)))
            log_info(f"Created input file: {ip}")

    # Receipt
    if write_receipt:
        receipt_path = _emit_receipt(
            out, created
        )  # <-- KLUCZOWE: nowa nazwa zmiennej, nie nadpisuj write_receipt
        created.append(
            Generated(
                kind="receipt",
                format=None,
                path=receipt_path,
                sha256=_sha256_hex(receipt_path),
            )
        )
        log_info(f"Wrote provenance receipt: {receipt_path}")

    # Summary
    log_info(f"Total artifacts: {len(created)}")
    for it in created:
        log_info(f"Wrote: {it.path}")

    return [it.path for it in created]


# === CLI ======================================================= #


def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="generate_proofs",
        description="Generate (simulated/stub) proof artifacts into an output directory.",
    )
    p.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output directory for generated files.",
    )
    p.add_argument(
        "--mode",
        choices=["simulate", "stub"],
        default="simulate",
        help='Generation mode (default: "simulate").',
    )
    p.add_argument(
        "--formats",
        nargs="*",
        choices=sorted(FORMAT_TO_FILE.keys()),
        default=None,
        help="Formats to generate (space-separated), e.g. --formats drat lfsc. Default: both.",
    )
    p.add_argument(
        "--with-inputs",
        action="store_true",
        help="Also create input.smt2 and input.cnf.",
    )
    p.add_argument(
        "--seed",
        type=int,
        default=None,
        help="Optional RNG seed for reproducible nonce in simulate mode.",
    )
    p.add_argument(
        "--receipt",
        action="store_true",
        help=f"Write provenance receipt JSON ({RECEIPT_FILE}).",
    )
    return p


def main(argv: Iterable[str] | None = None) -> int:
    log_info, _log_success, log_error = _lazy_console()

    try:
        args = _build_arg_parser().parse_args(list(argv) if argv is not None else None)
        files = generate_proofs(
            args.out,
            formats=args.formats,
            mode=args.mode,
            with_inputs=args.with_inputs,
            seed=args.seed,
            write_receipt=args.receipt,
        )
        if not files:
            log_error("No artifacts generated.")
            return 2
        return 0
    except Exception as exc:  # pragma: no cover
        log_error(f"Generation failed: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
