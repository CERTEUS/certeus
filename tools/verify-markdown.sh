#!/usr/bin/env bash
set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR
# CERTEUS • Control • Lint • verify-markdown
# PL: Waliduje puste linie wokół nagłówków i list w plikach Markdown.
# EN: Validates blank lines around headings and lists in Markdown files.
# File: tools/verify-markdown.sh
# Repo: CERTEUS/control • License: MIT
# Sections: PURPOSE • USAGE • MAIN

err=0
check_file() {
  local f="$1"
  awk -v file="$f" '
  function report(n,msg){ printf("%s:%d: %s\n", file, n, msg) }
  BEGIN{ prev=""; in_list=0; prev_was_heading=0 }
  {
    line=$0
    is_blank = (match(line, /^\s*$/) > 0)
    is_heading = (match(line, /^#{1,6}[[:space:]]/) > 0)
    is_list = (match(line, /^\s*([-*]|[0-9]+\.)[[:space:]]/) > 0)

    if (prev_was_heading && !is_blank) { report(NR-1, "Brak pustej linii po nagłówku") }
    prev_was_heading=0

    if (is_heading && NR>1 && prev !~ /^\s*$/) { report(NR, "Brak pustej linii przed nagłówkiem") }
    if (is_heading) { prev_was_heading=1 }

    if (is_list) {
      if (!in_list) {
        if (NR>1 && prev !~ /^\s*$/) { report(NR, "Brak pustej linii przed listą") }
        in_list=1
      }
    } else {
      if (in_list) {
        if (!is_blank) { report(NR-1, "Brak pustej linii po liście") }
        in_list=0
      }
    }

    prev=line
  }
  ' "$f" || true
}

shopt -s nullglob globstar

# Zidentyfikuj ścieżki submodułów i pomijaj je w weryfikacji
declare -a submods=()
while read -r _ path; do
  [[ -n "$path" ]] && submods+=("$path")
done < <(git config -f .gitmodules --get-regexp path 2>/dev/null || true)

# Zbierz wszystkie pliki Markdown poza katalogami wewnętrznymi
files=(**/*.md)
for f in "${files[@]}"; do
  # Pomijaj dokumenty wewnętrzne, cache i submoduły
  [[ "$f" == .control/* ]] && continue
  [[ "$f" == AGENT.md ]] && continue
  [[ "$f" == **/.git/** ]] && continue
  # Pomiń wszystkie ścieżki znajdujące się w submodułach
  for sp in "${submods[@]}"; do
    if [[ "$f" == "$sp" || "$f" == "$sp"/* ]]; then
      continue 2
    fi
  done

  out=$(check_file "$f") || true
  if [[ -n "$out" ]]; then printf '%s\n' "$out"; err=1; fi
done

exit $err
