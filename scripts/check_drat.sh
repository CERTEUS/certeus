#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                    CERTEUS - DRAT Checker                   |
# +-------------------------------------------------------------+
# | PLIK / FILE: scripts/check_drat.sh                          |
# | ROLA / ROLE:                                                |
# |  PL: Stub do weryfikacji dowodu w formacie DRAT.            |
# |  EN: Stub for verifying DRAT-format proof.                  |
# +-------------------------------------------------------------+

# === BEZPIECZEŃSTWO / SAFETY ===
set -Eeuo pipefail
IFS=$'\n\t'

# === KOLORY / COLORS (auto-disable on non-TTY) ===
if [[ -t 1 && -z "${NO_COLOR:-}" ]]; then
  BLUE=$'\033[1;34m'; GREEN=$'\033[1;32m'; RED=$'\033[1;31m'; GRAY=$'\033[0;90m'; RESET=$'\033[0m'
else
  BLUE=''; GREEN=''; RED=''; GRAY=''; RESET=''
fi

# === LOGOWANIE / LOGGING ===
QUIET=0
log()   { (( QUIET )) || printf "%b%s%b\n" "$1" "$2" "$RESET"; }
info()  { log "$BLUE"  "[INFO] $*"; }
ok()    { log "$GREEN" "[OK]   $*"; }
err()   { log "$RED"   "[ERR]  $*" >&2; }
dbg()   { (( QUIET )) || log "$GRAY" "[DBG]  $*"; }

# === OBSŁUGA BŁĘDÓW / ERROR TRAP ===
trap 'err "Unexpected error on line $LINENO"; exit 99' ERR

# === UŻYCIE / USAGE ===
usage() {
  cat <<'EOF'
PL: Użycie:
  scripts/check_drat.sh -d <katalog_z_dowodami> [-f <plik_drat>] [-q]
EN: Usage:
  scripts/check_drat.sh -d <proof_dir>           [-f <drat_file>] [-q]

Opcje / Options:
  -d DIR   PL: Katalog z dowodami (wymagane).    EN: Proofs directory (required).
  -f FILE  PL: Nazwa pliku DRAT (domyślnie: z3.drat).
           EN: DRAT file name (default: z3.drat).
  -q       PL: Tryb cichy (tylko błędy).         EN: Quiet mode (errors only).
  -h       PL: Pomoc.                            EN: Help.

Kody wyjścia / Exit codes:
   0 = OK,  2 = brak pliku / file not found,  3 = złe argumenty / bad args, 99 = inny błąd / other error.
EOF
}

# === PARAMETRY / PARAMS ===
PROOF_DIR=""
DRAT_FILE="z3.drat"

# Proste parsowanie krótkich flag (POSIX getopts)
while getopts ":d:f:qh" opt; do
  case "$opt" in
    d) PROOF_DIR=$OPTARG ;;
    f) DRAT_FILE=$OPTARG ;;
    q) QUIET=1 ;;
    h) usage; exit 0 ;;
    \?) err "Nieznana opcja / Unknown option: -$OPTARG"; usage; exit 3 ;;
    :)  err "Opcja wymaga wartości / Option requires an argument: -$OPTARG"; usage; exit 3 ;;
  esac
done
shift $((OPTIND-1))

# Walidacja / Validation
[[ -n "$PROOF_DIR" ]] || { err "Brak -d DIR / Missing -d DIR"; usage; exit 3; }
[[ -d "$PROOF_DIR"  ]] || { err "Katalog nie istnieje / Directory does not exist: $PROOF_DIR"; exit 2; }

TARGET="${PROOF_DIR%/}/${DRAT_FILE}"

info "PL: Sprawdzanie DRAT w: ${TARGET} | EN: Checking DRAT at: ${TARGET}"

if [[ -f "$TARGET" ]]; then
  ok "PL: Plik DRAT istnieje: $TARGET | EN: DRAT file exists: $TARGET"
  # PL: Tu podłączysz właściwy checker, np. drat-trim / EN: Hook real checker here, e.g., drat-trim
  # Przykład / Example:
  # if command -v drat-trim >/dev/null 2>&1; then
  #   info "PL: Uruchamiam drat-trim... | EN: Running drat-trim..."
  #   drat-trim "$cnf_file" "$TARGET" || { err "drat-trim failed"; exit 1; }
  # fi
  exit 0
else
  err "PL: Nie znaleziono pliku DRAT: $TARGET | EN: DRAT file not found: $TARGET"
  exit 2
fi
