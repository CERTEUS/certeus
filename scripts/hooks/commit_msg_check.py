# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/hooks/commit_msg_check.py                     |
# | ROLE: Enforce Conventional Commits in commit messages       |
# | PLIK: scripts/hooks/commit_msg_check.py                     |
# | ROLA: Wymusza format Conventional Commits w opisach commitów|
# +-------------------------------------------------------------+

"""

PL: Prosty walidator komunikatów commitów (Conventional Commits).
    - Dozwolone typy: feat, fix, chore, docs, ci, perf, refactor, test, style, build, revert.
    - Wzorzec nagłówka: `type(scope)?: subject` (max 72 znaków w subject).
    - Użycie (pre-commit, stage commit-msg): otrzymuje ściekę pliku z opisem.

EN: Simple Conventional Commits validator for commit messages.
    - Allowed types: feat, fix, chore, docs, ci, perf, refactor, test, style, build, revert.
    - Header pattern: `type(scope)?: subject` (subject up to 72 chars).
    - Usage (pre-commit, commit-msg stage): receives commit message file path.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import re
import sys

# === KONFIGURACJA / CONFIGURATION ===

ALLOWED = {
    "feat",
    "fix",
    "chore",
    "docs",
    "ci",
    "perf",
    "refactor",
    "test",
    "style",
    "build",
    "revert",
}
HEADER_RE = re.compile(r"^(?P<type>[a-z]+)(\([^)]+\))?(!)?:\s(?P<subject>.+)$")

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def validate(message: str) -> tuple[bool, str | None]:
    lines = [ln for ln in message.splitlines() if ln.strip() != ""]
    if not lines:
        return False, "Empty commit message"
    header = lines[0].strip()
    m = HEADER_RE.match(header)
    if not m:
        return False, ("Invalid header. Expected 'type(scope)?: subject'. Allowed types: " + ", ".join(sorted(ALLOWED)))
    ctype = m.group("type")
    if ctype not in ALLOWED:
        return False, f"Invalid type '{ctype}'. Allowed: {', '.join(sorted(ALLOWED))}"
    subject = m.group("subject").strip()
    if len(subject) > 72:
        return False, "Subject too long (>72 chars)"
    return True, None


def main(argv: list[str]) -> int:
    if not argv:
        print("No commit message file provided", file=sys.stderr)
        return 1
    path = Path(argv[-1])
    try:
        text = path.read_text(encoding="utf-8")
    except Exception as e:
        print(f"Cannot read commit message: {e}", file=sys.stderr)
        return 1
    ok, err = validate(text)
    if not ok:
        print("\nConventional Commits check failed:\n", file=sys.stderr)
        print(f"  {err}", file=sys.stderr)
        print("\nExamples:", file=sys.stderr)
        print("  feat(api): add qtm presets endpoint", file=sys.stderr)
        print("  fix(ledger): handle empty bundle case", file=sys.stderr)
        print("  chore(ci): enable ci-gates as required check", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
