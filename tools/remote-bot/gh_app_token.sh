#!/usr/bin/env bash
set -euo pipefail

# Generuje JWT dla GitHub App i pobiera access token instalacji.
# Obsługa źródeł klucza:
# - GH_APP_PRIVATE_KEY_B64 (base64 całego PEM)
# - GH_APP_PRIVATE_KEY (PEM z \n lub prawdziwymi nowymi liniami)
# - GH_APP_PRIVATE_KEY_PATH (ścieżka do PEM)
# - domyślnie: .control/keys/github-app-private-key.pem
# Wymagane: GH_APP_ID, GH_APP_INSTALLATION_ID
#
# Użycie:
#   tools/gh_app_token.sh                 # wypisze sam token
#   tools/gh_app_token.sh --export        # eksport zmiennych do eval
#   tools/gh_app_token.sh --json          # zwróci pełne JSON z GitHub
#   tools/gh_app_token.sh --jwt           # wypisze sam JWT (debug)
#   tools/gh_app_token.sh --check         # sprawdzenie zależności i env
#
# Przykłady:
#   eval "$(tools/gh_app_token.sh --export)" && gh repo list
#   GITHUB_TOKEN=$(tools/gh_app_token.sh) git ls-remote https://github.com/owner/repo.git

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
get_repo_root() {
  if command -v git >/dev/null 2>&1; then
    if git -C "${SCRIPT_DIR}" rev-parse --show-toplevel >/dev/null 2>&1; then
      git -C "${SCRIPT_DIR}" rev-parse --show-toplevel
      return
    fi
  fi
  (cd "${SCRIPT_DIR}/../.." 2>/dev/null && pwd) || (cd "${SCRIPT_DIR}/.." 2>/dev/null && pwd)
}
REPO_ROOT="$(get_repo_root)"

load_env() {
  # Pozwól na .env w repo (ignorowany przez git)
  if [[ -f "${REPO_ROOT}/.env" ]]; then
    set -o allexport
    # shellcheck disable=SC1090
    source "${REPO_ROOT}/.env"
    set +o allexport
  fi
}

# Jednolinijkowy pakiet sekretów: .control/remote-bot.secret
# Formaty wspierane (jedna linia):
# - APP_ID:INSTALLATION_ID:BASE64_PEM
# - GH_APP_ID=.. GH_APP_INSTALLATION_ID=.. GH_APP_PRIVATE_KEY_B64=..   (spacje/;/& jako separator)
# - json:{"app_id":123,"installation_id":456,"private_key_b64":"..."}
# - b64:<base64 z powyższego JSON>
load_secret_bundle_if_present() {
  local secret_path="${REPO_ROOT}/.control/remote-bot.secret"
  [[ -f "${secret_path}" ]] || return 0

  # Nie nadpisuj jeśli już ustawione
  if [[ -n "${GH_APP_ID:-}" && -n "${GH_APP_INSTALLATION_ID:-}" && ( -n "${GH_APP_PRIVATE_KEY_B64:-}" || -n "${GH_APP_PRIVATE_KEY:-}" || -n "${GH_APP_PRIVATE_KEY_PATH:-}" ) ]]; then
    return 0
  fi

  local line
  line=$(head -n1 "${secret_path}" | tr -d '\r' | sed 's/^\s\+//;s/\s\+$//')
  [[ -n "${line}" ]] || return 0

  case "${line}" in
    json:*)
      line=${line#json:}
      if command -v jq >/dev/null 2>&1; then
        export GH_APP_ID=$(printf '%s' "${line}" | jq -r '.app_id // .GH_APP_ID')
        export GH_APP_INSTALLATION_ID=$(printf '%s' "${line}" | jq -r '.installation_id // .GH_APP_INSTALLATION_ID')
        export GH_APP_PRIVATE_KEY_B64=$(printf '%s' "${line}" | jq -r '.private_key_b64 // .GH_APP_PRIVATE_KEY_B64')
      else
        # Fallback python
        eval "$(python3 - <<'PY'
import sys, json
data=json.loads(sys.stdin.read())
def p(k):
  v=data.get(k) or data.get(k.upper())
  if v is None: v=''
  print(f'export {k.upper()}={v}')
p('app_id'); p('installation_id'); p('private_key_b64')
PY
        <<<'"${line}"')"
        # Mapuj nazwy
        export GH_APP_PRIVATE_KEY_B64="${PRIVATE_KEY_B64:-${GH_APP_PRIVATE_KEY_B64:-}}"
      fi
      ;;
    b64:*)
      line=${line#b64:}
      local json
      json=$(printf '%s' "${line}" | base64 -d 2>/dev/null || true)
      if [[ -n "${json}" ]]; then
        if command -v jq >/dev/null 2>&1; then
          export GH_APP_ID=$(printf '%s' "${json}" | jq -r '.app_id // .GH_APP_ID')
          export GH_APP_INSTALLATION_ID=$(printf '%s' "${json}" | jq -r '.installation_id // .GH_APP_INSTALLATION_ID')
          export GH_APP_PRIVATE_KEY_B64=$(printf '%s' "${json}" | jq -r '.private_key_b64 // .GH_APP_PRIVATE_KEY_B64')
        else
          eval "$(python3 - <<'PY'
import sys, json
data=json.loads(sys.stdin.read())
for k in ('app_id','GH_APP_ID'):
  if k in data: print('export GH_APP_ID='+str(data[k])); break
for k in ('installation_id','GH_APP_INSTALLATION_ID'):
  if k in data: print('export GH_APP_INSTALLATION_ID='+str(data[k])); break
for k in ('private_key_b64','GH_APP_PRIVATE_KEY_B64'):
  if k in data: print('export GH_APP_PRIVATE_KEY_B64='+str(data[k])); break
PY
          <<<'"${json}"')"
        fi
      fi
      ;;
    *=*)
      # Klucze w linii rozdzielone spacją/;&
      line=$(printf '%s' "${line}" | tr ';&' '  ')
      # shellcheck disable=SC2206
      local parts=( ${line} )
      local kv k v
      for kv in "${parts[@]}"; do
        k=${kv%%=*}; v=${kv#*=}
        case "$k" in
          GH_APP_ID) export GH_APP_ID="$v" ;;
          GH_APP_INSTALLATION_ID) export GH_APP_INSTALLATION_ID="$v" ;;
          GH_APP_PRIVATE_KEY_B64) export GH_APP_PRIVATE_KEY_B64="$v" ;;
          app_id) export GH_APP_ID="$v" ;;
          installation_id) export GH_APP_INSTALLATION_ID="$v" ;;
          private_key_b64) export GH_APP_PRIVATE_KEY_B64="$v" ;;
        esac
      done
      ;;
    *)
      # APP_ID:INSTALLATION_ID:BASE64_PEM
      IFS=':' read -r _app _inst _b64 <<<"${line}"
      if [[ -n "${_app}" && -n "${_inst}" && -n "${_b64}" ]]; then
        export GH_APP_ID="${_app}"
        export GH_APP_INSTALLATION_ID="${_inst}"
        export GH_APP_PRIVATE_KEY_B64="${_b64}"
      fi
      ;;
  esac
}

need() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "Brak narzędzia: $1" >&2
    return 1
  }
}

b64url_encode() {
  # base64url bez paddingu
  openssl base64 -e -A | tr '+/' '-_' | tr -d '='
}

write_key_if_env() {
  # Zwraca ścieżkę do PEM w stdout
  local key_path="${REPO_ROOT}/.control/keys/github-app-private-key.pem"
  mkdir -p "${REPO_ROOT}/.control/keys"
  umask 077

  if [[ -n "${GH_APP_PRIVATE_KEY_B64:-}" ]]; then
    printf '%s' "${GH_APP_PRIVATE_KEY_B64}" | tr -d '\n' | base64 -d >"${key_path}"
    echo "${key_path}"
    return 0
  fi

  if [[ -n "${GH_APP_PRIVATE_KEY:-}" ]]; then
    # Zamień dosłowne \n na nowe linie, jeśli występują
    printf '%s' "${GH_APP_PRIVATE_KEY}" | sed 's/\\n/\n/g' >"${key_path}"
    echo "${key_path}"
    return 0
  fi

  if [[ -n "${GH_APP_PRIVATE_KEY_PATH:-}" ]]; then
    echo "${GH_APP_PRIVATE_KEY_PATH}"
    return 0
  fi

  # Ostatecznie spróbuj domyślnej lokalizacji
  if [[ -f "${key_path}" ]]; then
    echo "${key_path}"
    return 0
  fi

  echo "Nie znaleziono klucza prywatnego. Ustaw GH_APP_PRIVATE_KEY(_B64)/GH_APP_PRIVATE_KEY_PATH lub wklej PEM do ${key_path}" >&2
  return 1
}

make_jwt() {
  local app_id="$1" key_file="$2"
  # iat: teraz-60s (bufor), exp: do 9min (540s)
  local now iat exp
  now=$(date +%s)
  iat=$((now-60))
  exp=$((now+540))

  local header payload header_b64 payload_b64 unsigned sig jwt iss
  header='{"alg":"RS256","typ":"JWT"}'

  if [[ "${app_id}" =~ ^[0-9]+$ ]]; then
    iss="${app_id}"
  else
    iss="\"${app_id}\""
  fi

  payload=$(printf '{"iat":%d,"exp":%d,"iss":%s}' "${iat}" "${exp}" "${iss}")

  header_b64=$(printf '%s' "${header}" | b64url_encode)
  payload_b64=$(printf '%s' "${payload}" | b64url_encode)
  unsigned="${header_b64}.${payload_b64}"

  sig=$(printf '%s' "${unsigned}" | openssl dgst -sha256 -sign "${key_file}" | b64url_encode)
  jwt="${unsigned}.${sig}"

  printf '%s' "${jwt}"
}

get_installation_token_json() {
  local jwt="$1" inst_id="$2"
  curl -sS -X POST \
    -H "Authorization: Bearer ${jwt}" \
    -H "Accept: application/vnd.github+json" \
    "https://api.github.com/app/installations/${inst_id}/access_tokens"
}

json_get() {
  local key="$1"
  if command -v jq >/dev/null 2>&1; then
    jq -r ".${key}"
  else
    python3 - "$key" <<'PY'
import sys, json
k = sys.argv[1]
data = json.load(sys.stdin)
v = data
for part in k.split('.'):
    v = v.get(part, None) if isinstance(v, dict) else None
print('' if v is None else v)
PY
  fi
}

print_help() {
  sed -n '1,80p' "$0" | sed -n '1,40p' | sed 's/^# \{0,1\}//'
}

main() {
  load_env
  load_secret_bundle_if_present

  local mode="token" # token|export|json|jwt|check
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --export) mode="export" ; shift ;;
      --json)   mode="json"   ; shift ;;
      --jwt)    mode="jwt"    ; shift ;;
      --check)  mode="check"  ; shift ;;
      -h|--help) print_help; exit 0 ;;
      *) echo "Nieznana opcja: $1" >&2; exit 2 ;;
    esac
  done

  if [[ "${mode}" == "check" ]]; then
    local ok=0
    for bin in curl openssl; do if ! need "$bin"; then ok=1; fi; done
    if ! command -v jq >/dev/null 2>&1 && ! command -v python3 >/dev/null 2>&1; then
      echo "Wymagany jq lub python3 do parsowania JSON." >&2; ok=1
    fi
    if [[ -z "${GH_APP_ID:-}" || -z "${GH_APP_INSTALLATION_ID:-}" ]]; then
      echo "Brak GH_APP_ID lub GH_APP_INSTALLATION_ID w env/.env" >&2; ok=1
    fi
    if [[ $ok -ne 0 ]]; then exit 1; else echo "OK"; exit 0; fi
  fi

  : "${GH_APP_ID:?Ustaw GH_APP_ID (App ID)}"
  : "${GH_APP_INSTALLATION_ID:?Ustaw GH_APP_INSTALLATION_ID (Installation ID)}"

  local key_file jwt json token expires
  key_file=$(write_key_if_env)
  jwt=$(make_jwt "${GH_APP_ID}" "${key_file}")

  if [[ "${mode}" == "jwt" ]]; then
    printf '%s\n' "${jwt}"
    exit 0
  fi

  json=$(get_installation_token_json "${jwt}" "${GH_APP_INSTALLATION_ID}")
  # Szybka walidacja błędów
  if echo "${json}" | grep -q '"message"'; then
    echo "GitHub API error:" >&2
    echo "${json}" | sed 's/^/  /' >&2
    exit 1
  fi

  case "${mode}" in
    json)
      printf '%s\n' "${json}"
      ;;
    export)
      token=$(printf '%s' "${json}" | json_get token)
      expires=$(printf '%s' "${json}" | json_get expires_at)
      printf 'export GITHUB_TOKEN=%q\n' "${token}"
      printf 'export GH_TOKEN=%q\n' "${token}"
      printf 'export GITHUB_TOKEN_EXPIRES_AT=%q\n' "${expires}"
      ;;
    token|*)
      token=$(printf '%s' "${json}" | json_get token)
      printf '%s\n' "${token}"
      ;;
  esac
}

main "$@"
