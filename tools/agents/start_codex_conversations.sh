#!/usr/bin/env bash
set -Eeuo pipefail

# Starter: 10 równoległych sesji (A0..A9) dla Codex CLI na bazie promptów.

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
PROMPTS_DIR="$ROOT_DIR/.control/plans/agents"

echo "[INFO] Prompty: $PROMPTS_DIR"
ls -1 "$PROMPTS_DIR" | sed 's/^/- /'

cat <<'TXT'

Instrukcja uruchomienia (manualna):

1) Zaloguj się do Codex CLI i uruchom kontener dev (Ubuntu) zgodnie z AGENT.md.
2) Dla każdego Agenta (A0..A9) otwórz osobną sesję i wklej zawartość odpowiedniego pliku:
   .control/plans/agents/A0.prompt.md ... A9.prompt.md
3) Pracuj zgodnie z „Loop Until Green”: implementacja w certeus, lint+test lokalnie, PR, czekaj na zielone checki.

Uwaga: Skrypt jest tylko przewodnikiem — nie wykonuje operacji w Codex CLI automatycznie.

TXT

echo "[OK] Gotowe. Otwórz sesje Codex i wczytaj prompty A0..A9."

