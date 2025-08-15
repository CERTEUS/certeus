#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                    CERTEUS - LFSC Checker                   |
# +-------------------------------------------------------------+
# | PLIK / FILE: scripts/check_lfsc.sh                          |
# | ROLA / ROLE:                                                |
# |  PL: Stub do weryfikacji dowodu w formacie LFSC.            |
# |  EN: Stub for verifying LFSC-format proof.                  |
# +-------------------------------------------------------------+

# === BEZPIECZEŃSTWO / SAFETY ===
set -Eeuo pipefail
IFS=$'\n\t'

# === KOLORY / COLORS ===
if [[ -t 1 && -z "${NO_COLOR:-}" ]]; then
  BLUE=$'\033[1;34m'; GREEN=$'\033[1;32m'; RED=$'\033[1;31m'; GRAY=$'\033[0;90m'; RESET=$'\033[0m'
else
  BLUE=''; GREEN=''; RED=''; GRAY=''; RESET=''
fi

# === LOGI / LOGGING ===
QUIET=0
log()   { (( QUIET )) || printf "%b%s%b\n" "$1" "$2" "$RESET"; }
info()  { log "$BLUE"  "[INFO] $*"; }
ok()    { log "$GREEN" "[OK]   $*"; }
err()   { log "$RED"   "[ERR]  $*" >&2; }

trap 'err "PL: Niespodziewany błąd w linii $LINENO | EN: Unexpected error on line $LINENO"; exit 99' ERR

# === UŻYCIE / USAGE ===
usage() {
  cat <<'EOF'
PL: Użycie:
  scripts/check_lfsc.sh -d <katalog_z_dowodami> [-f <plik_lfsc>] [-q]
EN: Usage:
  scripts/check_lfsc.sh -d <proof_dir>           [-f <lfsc_file>] [-q]

Opcje / Options:
  -d DIR   PL: Katalog z dowodami (wymagane).    EN: Proofs directory (required).
  -f FILE  PL: Nazwa pliku LFSC (domyślnie: cvc5.lfsc).
           EN: LFSC file name (default: cvc5.lfsc).
  -q       PL: Tryb cichy (tylko błędy).         EN: Quiet mode (errors only).
  -h       PL: Pomoc.                            EN: Help.

Kody wyjścia / Exit codes:
   0 = OK,  2 = brak pliku / file not found,  3 = złe argumenty / bad args, 99 = inny błąd / other error.
EOF
}

# === PARAMETRY ===
PROOF_DIR=""
LFSC_FILE="cvc5.lfsc"

while getopts ":d:f:qh" opt; do
  case "$opt" in
    d) PROOF_DIR=$OPTARG ;;
    f) LFSC_FILE=$OPTARG ;;
    q) QUIET=1 ;;
    h) usage; exit 0 ;;
    \?) err "Nieznana opcja / Unknown option: -$OPTARG"; usage; exit 3 ;;
    :)  err "Opcja wymaga wartości / Option requires an argument: -$OPTARG"; usage; exit 3 ;;
  esac
done
shift $((OPTIND-1))

[[ -n "$PROOF_DIR" ]] || { err "Brak -d DIR / Missing -d DIR"; usage; exit 3; }
[[ -d "$PROOF_DIR"  ]] || { err "Katalog nie istnieje / Directory does not exist: $PROOF_DIR"; exit 2; }

TARGET="${PROOF_DIR%/}/${LFSC_FILE}"

info "PL: Sprawdzanie LFSC w: ${TARGET} | EN: Checking LFSC at: ${TARGET}"

if [[ -f "$TARGET" ]]; then
  ok "PL: Plik LFSC istnieje: $TARGET | EN: LFSC file exists: $TARGET"
  # PL: Tu podłączysz właściwy checker LFSC / EN: Hook real LFSC checker here
  exit 0
else
  err "PL: Nie znaleziono pliku LFSC: $TARGET | EN: LFSC file not found: $TARGET"
  exit 2
fi
