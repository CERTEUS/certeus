#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: repo_to_packs.py                                              |
# | ROLE:                                                               |
# |  PL: Budowa "packów" z repo dla AI (Claude/GPT/Gemini),             |
# |      teraz szybka enumeracja plików przez `git ls-files`,           |
# |      bezpieczne cięcie, manifest i logi postępu.                    |
# |      DODANE: pełny spis repo (dirs+files) do MANIFEST.json          |
# |              oraz REPO_TREE.md w formacie markdown.                 |
# |  EN: Build AI packs (Claude/GPT/Gemini) using fast `git ls-files`   |
# |      enumeration, safe chunking, manifest, and progress logging.    |
# |      ADDED: full repo inventory (dirs+files) in MANIFEST.json       |
# |             and human-readable REPO_TREE.md (markdown).             |
# +=====================================================================+
"""
PL: Generator paczek tekstowych z repozytorium (pack_XX.txt) dla modeli
    konwersacyjnych. Szybkie pozyskiwanie listy plików przez `git ls-files`
    (tracked + untracked, nieignorowane), fallback do skanowania gdy brak Gita.
    Honoruje include/exclude, wykrywa binaria, tnie pliki na bezpiecznych
    granicach, buduje manifesty i raportuje postęp w trybie --verbose.

EN: Text-pack generator for chat models. Uses `git ls-files` to fetch
    non-ignored files in one shot (tracked + untracked), with a no-git
    fallback. Honors include/exclude, detects binaries, safe chunking,
    builds manifests, and prints progress with --verbose.

ADD: Generates a complete repository inventory for machines (MANIFEST.json)
     and a human-readable full tree (REPO_TREE.md).
"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

import argparse
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
import fnmatch
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Any

BANNER = (
    "+=============================================================+\n"
    "|                       CERTEUS — HEART                        |\n"
    "+=============================================================+\n"
)

# Defaults tuned for Claude/GPT/Gemini typical context windows
DEFAULT_PACK_CHARS = 250_000
DEFAULT_FILE_CHUNK = 80_000
DEFAULT_OVERLAP = 2_000

# Extensions treated as binary; .pdf etc. are ubiquitous.
BINARY_EXTENSIONS = {
    ".pdf",
    ".png",
    ".jpg",
    ".jpeg",
    ".gif",
    ".webp",
    ".zip",
    ".7z",
    ".gz",
    ".bz2",
    ".xz",
    ".exe",
    ".dll",
    ".so",
    ".dylib",
    ".pkl",
    ".onnx",
    ".mp3",
    ".mp4",
    ".mov",
    ".avi",
    ".docx",
    ".xlsx",
    ".pptx",
}

# Prefer text extensions (others still accepted if no NULs)
PREFERRED_TEXT_EXTENSIONS = {
    ".py",
    ".md",
    ".txt",
    ".json",
    ".yaml",
    ".yml",
    ".toml",
    ".ini",
    ".cfg",
    ".gitignore",
    ".gitattributes",
    ".editorconfig",
    ".smt2",
    ".lfsc",
    ".drat",
    ".sh",
    ".ps1",
    ".bat",
    ".html",
    ".css",
    ".js",
    ".ts",
    ".lex",
}

# Additional excludes beyond .gitignore to keep packs clean.
DEFAULT_EXCLUDE_GLOBS = [
    ".git/",
    ".github/",
    ".gitlab/",
    "__pycache__/",
    ".venv/",
    "venv/",
    "env/",
    "dist/",
    "build/",
    "out/",
    "exports/",
    "artifacts/",
    "reports/",
    "node_modules/",
    ".idea/",
    ".vscode/",
    ".uv/",
    "uv.lock",
    "static/previews/",
    "proofs/",
    "htmlcov/",
    "coverage.xml",
    "packs/jurisdictions/PL/flags/",
    "sample.txt",
    "sample.pdf",
]


@dataclass(frozen=True)
class FileEntry:
    rel_path: str
    size: int


def _has_git(root: Path) -> bool:
    """Return True if git is available and repo has a .git directory."""
    try:
        if not (root / ".git").exists():
            return False
        subprocess.run(
            ["git", "--version"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        return True
    except Exception:
        return False


def git_ls_visible_files(root: Path, verbose: bool) -> list[Path]:
    """
    PL: Zwróć listę ścieżek (Path) widocznych wg Gita:
        tracked + untracked, nieignorowane (exclude-standard).
    EN: Return visible file paths via Git (tracked + untracked, non-ignored).
    """
    # --cached: tracked; --others: untracked; --exclude-standard: obey .gitignore
    cmd = [
        "git",
        "-C",
        str(root),
        "ls-files",
        "-z",
        "--cached",
        "--others",
        "--exclude-standard",
    ]
    t0 = time.time()
    res = subprocess.run(cmd, capture_output=True, check=False)
    if res.returncode != 0:
        raise RuntimeError("git ls-files failed; is this a Git repo?")
    out = res.stdout
    parts = out.split(b"\x00")
    files: list[Path] = []
    for raw in parts:
        if not raw:
            continue
        # Git uses forward slashes; Path will normalize on Windows.
        files.append(root / raw.decode("utf-8", errors="ignore"))
    if verbose:
        dt = (time.time() - t0) * 1000
        print(f"[git] ls-files: {len(files)} files in {dt:.0f} ms")
    return files


def is_probably_binary(path: Path) -> bool:
    """Heuristic: extension + NUL sniff."""
    if path.suffix.lower() in BINARY_EXTENSIONS:
        return True
    try:
        with path.open("rb") as f:
            chunk = f.read(2048)
            if b"\x00" in chunk:
                return True
    except (FileNotFoundError, PermissionError, OSError):
        return True
    return False


def read_text_safely(path: Path) -> str:
    """Read text with tolerant encodings."""
    for enc in ("utf-8", "utf-8-sig", "latin-1"):
        try:
            return path.read_text(encoding=enc)
        except Exception:
            continue
    with path.open("r", encoding="utf-8", errors="ignore") as f:
        return f.read()


def iter_files_via_git(
    root: Path,
    includes: Sequence[str],
    excludes: Sequence[str],
    verbose: bool,
) -> Iterator[FileEntry]:
    """Enumerate non-ignored files via `git ls-files`, then apply include/exclude & binary check."""
    all_paths = git_ls_visible_files(root, verbose=verbose)
    include_patterns = list(includes) if includes else ["**/*"]
    exclude_patterns = list(excludes) if excludes else []
    total = 0
    for p in all_paths:
        if not p.is_file():
            continue
        rel = str(p.relative_to(root)).replace("\\", "/")
        if any(fnmatch.fnmatch(rel, ep) for ep in exclude_patterns):
            continue
        if not any(fnmatch.fnmatch(rel, ip) for ip in include_patterns):
            continue
        if is_probably_binary(p):
            continue
        size = p.stat().st_size
        total += 1
        if verbose and total % 500 == 0:
            print(f"[scan] {total} files accepted...")
        yield FileEntry(rel_path=rel, size=size)
    if verbose:
        print(f"[scan] total accepted files: {total}")


def iter_files_no_git(
    root: Path,
    includes: Sequence[str],
    excludes: Sequence[str],
    verbose: bool,
) -> Iterator[FileEntry]:
    """Fallback: rglob + simple pattern excludes (plus DEFAULT_EXCLUDE_GLOBS)."""
    include_patterns = list(includes) if includes else ["**/*"]
    exclude_patterns = list(excludes) + DEFAULT_EXCLUDE_GLOBS
    total = 0
    for p in sorted(root.rglob("*")):
        if not p.is_file():
            continue
        rel = str(p.relative_to(root)).replace("\\", "/")
        if any(
            rel.startswith(ep.rstrip("/"))
            for ep in exclude_patterns
            if ep.endswith("/")
        ):
            continue
        if any(
            fnmatch.fnmatch(rel, ep) for ep in exclude_patterns if not ep.endswith("/")
        ):
            continue
        if not any(fnmatch.fnmatch(rel, ip) for ip in include_patterns):
            continue
        if is_probably_binary(p):
            continue
        size = p.stat().st_size
        total += 1
        if verbose and total % 500 == 0:
            print(f"[scan-nogit] {total} files accepted...")
        yield FileEntry(rel_path=rel, size=size)
    if verbose:
        print(f"[scan-nogit] total accepted files: {total}")


def safe_boundary(text: str, start: int, search_window: int = 1200) -> int:
    """Find safe chunk boundary near `start`."""
    n = len(text)
    if start >= n:
        return n
    lo = max(0, start - search_window)
    hi = min(n, start + search_window)
    window = text[lo:hi]

    candidates: list[int] = []
    for pat in ("\n\n", "\n}\n", "\n]\n", "\n---\n"):
        idx = window.rfind(pat, 0, start - lo)
        if idx != -1:
            candidates.append(lo + idx + len(pat) - 1)
    if candidates:
        return max(candidates)

    for pat in ("\n\n", "\n}\n", "\n]\n", "\n---\n"):
        idx = window.find(pat, start - lo)
        if idx != -1:
            return lo + idx + len(pat) - 1

    nl_b = text.rfind("\n", lo, start)
    nl_f = text.find("\n", start, hi)
    if nl_f != -1:
        return nl_f
    if nl_b != -1:
        return nl_b
    return min(start, n)


def chunk_text(text: str, max_chars: int, overlap: int, safe: bool) -> list[str]:
    """Split text into chunks, optionally using safe boundaries."""
    chunks: list[str] = []
    i = 0
    n = len(text)
    if n <= max_chars:
        return [text]
    while i < n:
        end = i + max_chars
        if safe:
            end = safe_boundary(text, end)
        end = max(end, i + 1)
        chunk = text[i:end]
        chunks.append(chunk)
        if end >= n:
            break
        i = max(end - overlap, 0)
    return chunks


def file_header(rel_path: str) -> str:
    return f"\n\n===== FILE: {rel_path} =====\n```text\n"


def file_footer() -> str:
    return "\n```\n"


def pack_preamble() -> str:
    lines = [
        BANNER,
        "CERTEUS PACK — Context for AI assistants (Claude/GPT/Gemini).\n",
        "PL: Pliki repo są oddzielone '===== FILE: … ====='.\n",
        "EN: Files are delimited by '===== FILE: … ====='.\n",
        "Guidance: read sequentially; do not assume missing files exist; ",
        "respect file boundaries.\n\n",
    ]
    return "".join(lines)


# ===== NEW: full repo inventory (dirs+files) for machines & human tree =====


def _sha256_file(path: Path) -> str:
    """Streamed SHA-256 to avoid loading big files into memory."""
    h = hashlib.sha256()
    try:
        with path.open("rb") as f:
            for chunk in iter(lambda: f.read(1024 * 1024), b""):
                h.update(chunk)
    except Exception:
        # If unreadable, hash empty marker + path to keep deterministic output
        h.update(b"[UNREADABLE]")
        h.update(str(path).encode("utf-8", "ignore"))
    return h.hexdigest()


def collect_repo_inventory(root: Path) -> dict[str, Any]:
    """
    Build complete repo listing for MANIFEST.json:
    - dirs: list[str]      (relative paths, '/' suffix)
    - files: list[dict]    ({path, size, sha256, binary: bool})
    Note: we only skip '.git' tree to keep noise low.
    """
    dirs: list[str] = []
    files: list[dict[str, Any]] = []
    for cur, subdirs, fnames in os.walk(root):
        # skip .git internals
        subdirs[:] = [d for d in subdirs if d != ".git"]
        rel_dir = str(Path(cur).relative_to(root)).replace("\\", "/")
        rel_dir = "." if rel_dir == "." else rel_dir
        # add current dir (skip duplicate root line — we’ll still keep it for clarity)
        dirs.append("/" if rel_dir == "." else f"{rel_dir}/")
        for fn in sorted(fnames):
            p = Path(cur) / fn
            rel = str(p.relative_to(root)).replace("\\", "/")
            size = 0
            try:
                size = p.stat().st_size
            except Exception:
                pass
            is_bin = is_probably_binary(p)
            digest = _sha256_file(p)
            files.append(
                {
                    "path": rel,
                    "size": size,
                    "sha256": digest,
                    "binary": bool(is_bin),
                }
            )
    # sort stable
    dirs = sorted(set(dirs))
    files.sort(key=lambda x: x["path"])
    return {"dirs": dirs, "files": files}


def write_repo_tree_md(root: Path, out_dir: Path) -> Path:
    """
    Write human-readable tree (REPO_TREE.md).
    Shows full repository structure (excluding only '.git').
    """
    md_path = out_dir / "REPO_TREE.md"
    sio = io.StringIO()
    sio.write(BANNER)
    sio.write("# 📂 Repozytorium — pełne drzewo\n\n")
    sio.write(f"- Source: `{root}`\n")
    sio.write(f"- Generated (UTC): {datetime.now(UTC).isoformat()}\n\n")

    # Build a nested map for pretty printing
    tree: dict[str, Any] = {}
    total_files = 0

    for cur, subdirs, fnames in os.walk(root):
        subdirs[:] = [d for d in subdirs if d != ".git"]
        rel_dir = str(Path(cur).relative_to(root)).replace("\\", "/")
        parts = [] if rel_dir == "." else rel_dir.split("/")
        node = tree
        for part in parts:
            node = node.setdefault(part + "/", {})
        node.setdefault("__files__", [])
        for fn in sorted(fnames):
            node["__files__"].append(fn)
            total_files += 1

    def _emit(node: dict[str, Any], indent: int = 0) -> None:
        pad = "    " * indent
        # files
        for fn in node.get("__files__", []):
            sio.write(f"{pad}📄 {fn}\n")
        # subdirs
        for key in sorted(k for k in node.keys() if k != "__files__"):
            sio.write(f"{pad}📂 {key}\n")
            _emit(node[key], indent + 1)

    sio.write("📦 **Root**\n")
    _emit(tree, indent=1)
    sio.write(f"\n---\n**Łączna liczba plików:** {total_files}\n")
    md_path.write_text(sio.getvalue(), encoding="utf-8")
    return md_path


# ===== END NEW =====


def write_packs(
    root: Path,
    files: list[FileEntry],
    out_dir: Path,
    pack_chars: int,
    file_chunk: int,
    overlap: int,
    safe_boundaries: bool,
    verbose: bool,
) -> tuple[list[Path], dict]:
    """Build packs & manifest. Returns pack paths and manifest dict."""
    out_dir.mkdir(parents=True, exist_ok=True)
    pack_texts: list[str] = []
    pack_files: list[list[str]] = []
    current: list[str] = [pack_preamble()]
    current_files: list[str] = []
    current_len = len(current[0])

    total_chars = 0
    total_files = 0
    t0 = time.time()

    for idx_file, fe in enumerate(files, 1):
        path = root / fe.rel_path
        text = read_text_safely(path)
        total_files += 1
        f_chunks = chunk_text(
            text, max_chars=file_chunk, overlap=overlap, safe=safe_boundaries
        )
        for i_chunk, ch in enumerate(f_chunks, 1):
            hdr = file_header(
                fe.rel_path + (f" ::chunk:{i_chunk}" if len(f_chunks) > 1 else "")
            )
            block = f"{hdr}{ch}{file_footer()}"
            if current_len + len(block) > pack_chars and current_len > len(
                pack_preamble()
            ):
                pack_texts.append("".join(current))
                pack_files.append(current_files[:])
                total_chars += current_len
                current = [pack_preamble()]
                current_files = []
                current_len = len(current[0])
            current.append(block)
            current_files.append(fe.rel_path)
            current_len += len(block)
        if verbose and idx_file % 200 == 0:
            dt = time.time() - t0
            print(f"[pack] processed {idx_file}/{len(files)} files in {dt:.1f}s")

    if len(current) > 1:
        pack_texts.append("".join(current))
        pack_files.append(current_files[:])
        total_chars += current_len

    pad = max(2, len(str(len(pack_texts))))
    pack_paths: list[Path] = []
    for i, text in enumerate(pack_texts, 1):
        name = f"pack_{i:0{pad}d}.txt"
        p = out_dir / name
        p.write_text(text, encoding="utf-8")
        pack_paths.append(p)

    manifest: dict[str, Any] = {
        "banner": BANNER.strip(),
        "src_root": str(root),
        "created_utc": datetime.now(UTC).isoformat(),
        "params": {
            "pack_chars": pack_chars,
            "file_chunk": file_chunk,
            "overlap": overlap,
            "safe_boundaries": safe_boundaries,
        },
        "totals": {
            "files": total_files,
            "packs": len(pack_paths),
            "chars": total_chars,
        },
        "packs": [],
        # NEW — will be filled by collect_repo_inventory() in build()
        "repo": {"dirs": [], "files": []},
    }

    assert len(pack_paths) == len(pack_files), "pack paths/files length mismatch"

    for p, flist in zip(pack_paths, pack_files, strict=True):
        data = p.read_bytes()
        sha = hashlib.sha256(data).hexdigest()
        try:
            chars = len(data.decode("utf-8"))
        except UnicodeDecodeError:
            chars = len(data.decode("utf-8", errors="ignore"))
        manifest["packs"].append(
            {
                "file": p.name,
                "chars": chars,
                "sha256": sha,
                "files_count": len(set(flist)),
                "first": flist[0] if flist else None,
                "last": flist[-1] if flist else None,
            }
        )

    # Write machine manifest
    (out_dir / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8"
    )

    # Write short human manifest (summary of packs)
    md = io.StringIO()
    md.write(BANNER)
    md.write("# CERTEUS PACK MANIFEST\n\n")
    md.write(f"- Source: `{root}`\n")
    md.write(f"- Packs: {len(pack_paths)}\n")
    md.write(f"- Files (ingested): {total_files}\n")
    md.write(
        f"- Params: pack_chars={pack_chars}, file_chunk={file_chunk}, overlap={overlap}, safe={safe_boundaries}\n\n"
    )
    for rec in manifest["packs"]:
        sha12 = str(rec["sha256"])[:12]
        md.write(
            f"- **{rec['file']}** — chars: {rec['chars']}, files: {rec['files_count']}, sha256: `{sha12}…`\n"
        )
    (out_dir / "MANIFEST.md").write_text(md.getvalue(), encoding="utf-8")

    return pack_paths, manifest


def build(
    src: Path,
    out_dir: Path,
    pack_chars: int,
    file_chunk: int,
    overlap: int,
    safe_boundaries: bool,
    includes: Sequence[str],
    excludes: Sequence[str],
    use_git_ls: bool,
    verbose: bool,
) -> tuple[list[Path], dict]:
    """Deterministic pack builder with fast Git enumeration when available."""
    if use_git_ls and _has_git(src):
        files_iter = iter_files_via_git(src, includes, excludes, verbose=verbose)
    elif _has_git(src):
        # domyślnie i tak korzystamy z Git (najszybciej)
        files_iter = iter_files_via_git(src, includes, excludes, verbose=verbose)
    else:
        files_iter = iter_files_no_git(src, includes, excludes, verbose=verbose)

    files = list(files_iter)
    files.sort(key=lambda fe: fe.rel_path)

    # NEW: collect full repo inventory (machines) and REPO_TREE.md (human)
    repo_inv = collect_repo_inventory(src)

    pack_paths, manifest = write_packs(
        src, files, out_dir, pack_chars, file_chunk, overlap, safe_boundaries, verbose
    )

    # inject repo inventory into MANIFEST.json (machines)
    manifest["repo"] = repo_inv
    (out_dir / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8"
    )

    # write human-readable tree
    write_repo_tree_md(src, out_dir)

    return pack_paths, manifest


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Build AI-friendly packs from a repository (fast `git ls-files`, safe chunking, manifest, progress)."
        )
    )
    ap.add_argument("src", type=str, help="source repository root")
    ap.add_argument(
        "--out", type=str, default="ingest_repo", help="output directory for packs"
    )
    ap.add_argument(
        "--pack-chars",
        type=int,
        default=DEFAULT_PACK_CHARS,
        help="target characters per pack",
    )
    ap.add_argument(
        "--file-chunk", type=int, default=DEFAULT_FILE_CHUNK, help="per-file chunk size"
    )
    ap.add_argument(
        "--overlap", type=int, default=DEFAULT_OVERLAP, help="overlap between chunks"
    )
    ap.add_argument(
        "--include",
        action="append",
        default=[],
        help="glob to include (can be repeated)",
    )
    ap.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="glob to exclude (can be repeated)",
    )
    ap.add_argument(
        "--no-safe-boundaries",
        action="store_true",
        help="disable safe chunk boundaries",
    )
    ap.add_argument(
        "--git-ls-files", action="store_true", help="force using git ls-files (if repo)"
    )
    ap.add_argument("--verbose", action="store_true", help="print progress")
    return ap.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    ns = parse_args(sys.argv[1:] if argv is None else argv)
    src = Path(ns.src).resolve()
    out_dir = Path(ns.out).resolve()
    safe = not ns.no_safe_boundaries
    includes = ns.include or ["**/*"]
    excludes = ns.exclude or []

    t0 = time.time()
    packs, manifest = build(
        src=src,
        out_dir=out_dir,
        pack_chars=ns.pack_chars,
        file_chunk=ns.file_chunk,
        overlap=ns.overlap,
        safe_boundaries=safe,
        includes=includes,
        excludes=excludes,
        use_git_ls=ns.git_ls_files,
        verbose=ns.verbose,
    )

    print(BANNER, end="")
    print("CERTEUS — PACKS READY")
    print(f"Source: {src}")
    print(f"Output: {out_dir}")
    print(f"Packs:  {len(packs)}")
    print(f"Files (ingested):  {manifest['totals']['files']}")
    print(f"Repo entries (all files): {len(manifest.get('repo', {}).get('files', []))}")
    print(f"Chars:  {manifest['totals']['chars']}")
    print(f"Took:   {time.time() - t0:.1f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
