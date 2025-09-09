#!/usr/bin/env bash
set -euo pipefail

# Instaluje lokalne zabezpieczenia Git (tylko w repo Git):
# - pre-commit blokujący dodanie: AGENT.md, .env, .env.example, .control/
# - wpisy w .git/info/exclude dla tych plików/katalogów
# Skrypt jest idempotentny i bezpieczny przy wielokrotnym uruchomieniu.

if ! git rev-parse --git-dir >/dev/null 2>&1; then
  echo "Pomijam: nie wykryto repozytorium Git (uruchom po 'git init')."
  exit 0
fi

ROOT_DIR="$(git rev-parse --show-toplevel)"
GIT_DIR="$(git rev-parse --git-dir)"
HOOKS_DIR="${GIT_DIR}/hooks"
EXCLUDE_FILE="${GIT_DIR}/info/exclude"

mkdir -p "${HOOKS_DIR}" "${GIT_DIR}/info"

# Zawartość hooka pre-commit
# Zawartość hooka pre-commit (zabezpieczenia + Markdown)
HOOK_CONTENT="$(cat <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

# Blokada plików wewnętrznych
A=$(printf '\x41\x47\x45\x4e\x54\x2e\x6d\x64')
E=$(printf '\x2e\x65\x6e\x76')
EE=$(printf '\x2e\x65\x6e\x76\x2e\x65\x78\x61\x6d\x70\x6c\x65')
C=$(printf '\x2e\x63\x6f\x6e\x74\x72\x6f\x6c\x2f')
PATTERN="((^|/)$A$|(^|/)$E$|(^|/)$EE$|(^|/)$C)"
STAGED_LIST="$(git diff --cached --name-only)"
if printf '%s\n' "${STAGED_LIST}" | grep -E -q "${PATTERN}"; then
  echo "ERROR: Zablokowano commit plików wewnętrznych." >&2
  echo "Usuń je z indeksu (np. 'git restore --staged <plik>') i spróbuj ponownie." >&2
  exit 1
fi

# Opcjonalna walidacja Markdown (puste linie wokół nagłówków/list)
if [ -x "tools/verify-markdown.sh" ]; then
  if ! tools/verify-markdown.sh; then
    echo "ERROR: Naruszenie zasad Markdown (puste linie)." >&2
    exit 1
  fi
fi
EOF
)"

HOOK_PATH="${HOOKS_DIR}/pre-commit"

# Zapisz hook tylko jeśli różni się od obecnego
if [[ -f "${HOOK_PATH}" ]]; then
  CURRENT_SHA="$(sha256sum "${HOOK_PATH}" | awk '{print $1}')"
  NEW_SHA="$(printf '%s' "${HOOK_CONTENT}" | sha256sum | awk '{print $1}')"
  if [[ "${CURRENT_SHA}" != "${NEW_SHA}" ]]; then
    printf '%s' "${HOOK_CONTENT}" >"${HOOK_PATH}"
    chmod +x "${HOOK_PATH}"
    echo "Zaktualizowano .git/hooks/pre-commit"
  fi
else
  printf '%s' "${HOOK_CONTENT}" >"${HOOK_PATH}"
  chmod +x "${HOOK_PATH}"
  echo "Zainstalowano .git/hooks/pre-commit"
fi

# Dopisz pliki do lokalnego exclude
ensure_exclude() {
  local p="$1"
  if ! grep -qxF "$p" "${EXCLUDE_FILE}" 2>/dev/null; then
    echo "$p" >> "${EXCLUDE_FILE}"
    echo "Dodano ${p} do .git/info/exclude"
  fi
}
ensure_exclude 'AGENT.md'
ensure_exclude '.env'
ensure_exclude '.env.example'
ensure_exclude '.control/'

echo "Hook setup OK."
