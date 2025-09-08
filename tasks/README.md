# Tasks (A0–A9) — Orkiestracja i Loop Until Green

Ten katalog zawiera zadania dla agentów A0–A9 zgodnie z dokumentacją w `certeus/docs`.

- Źródło ról i zakresów: `certeus/docs/agent_read_mapa.md`
- Handoff/status: `certeus/docs/AGENTS/HANDOFF.md`
- Bramka G1: `certeus/docs/gates/G1_report.md`

Zasady pracy (skrót):

- Każdy agent realizuje swój plik `Ax.md` w pętli „Loop Until Green”.
- Każda zmiana musi mieć testy i przejść bramki CI w repo `certeus`.
- Zielone PR-checks są warunkiem merge (automatyczny merge po komplecie zielonych testów/gate’ów).

Uruchomienie 10 konwersacji Codex (po jednej na agenta):

1) Przygotowane prompty startowe: `.control/plans/agents/A0.prompt.md` … `A9.prompt.md`.
2) W kontenerze dev (Ubuntu) możesz uruchomić równoległe sesje, każdą inicjując odpowiednim promptem.
3) Minimalny skrypt pomocniczy: `tools/agents/start_codex_conversations.sh` (instrukcja, bez automatyki zewnętrznej).

Uwaga: pliki w `tasks/` są źródłem prawdy dla zakresu i DoD; spójne z dokumentacją w `certeus/` i nie zastępują wewnętrznych notatek w `.control/`.

