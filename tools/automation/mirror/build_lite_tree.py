from __future__ import annotations

import glob
import os
from pathlib import Path
import shutil
import sys


def build(out_dir: Path) -> None:
    root = Path(".")
    allowlist = root / "tools/automation/public_allowlist.txt"
    if not allowlist.exists():
        raise SystemExit("public_allowlist.txt not found")

    out_dir.mkdir(parents=True, exist_ok=True)

    # Copy allowed files/dirs (glob-aware) preserving structure
    with allowlist.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            for match in glob.glob(line, recursive=True):
                p = Path(match)
                if p.is_dir():
                    (out_dir / p).mkdir(parents=True, exist_ok=True)
                    continue
                (out_dir / p.parent).mkdir(parents=True, exist_ok=True)
                shutil.copy2(p, out_dir / p)

    # Public replacements
    src_readme = root / "tools/automation/mirror/README.public.md"
    src_mkdocs = root / "tools/automation/mirror/mkdocs.public.yml"
    src_license = root / "tools/automation/mirror/LICENSE-AGPL-3.0.txt"
    if src_readme.exists():
        shutil.copy2(src_readme, out_dir / "README.md")
    if src_mkdocs.exists():
        shutil.copy2(src_mkdocs, out_dir / "mkdocs.yml")
    if src_license.exists():
        shutil.copy2(src_license, out_dir / "LICENSE")

    # PROVENANCE
    provenance = out_dir / "PROVENANCE.md"
    sha = os.environ.get("GITHUB_SHA", "local")
    provenance.write_text(
        f"Source: CERTEUS/certeus@{sha}\nPublished: GENERATED\nMode: LITE (allowlist + squash)\n",
        encoding="utf-8",
    )


def main(argv: list[str]) -> int:
    out = Path(argv[1]) if len(argv) > 1 else Path("mirror_out_cli")
    build(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
