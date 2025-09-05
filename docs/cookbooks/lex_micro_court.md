# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/cookbooks/lex_micro_court.md                   |
# | ROLE: Project Markdown.                                     |
# | PLIK: docs/cookbooks/lex_micro_court.md                   |
# | ROLA: Cookbook LEXENITH / Micro‑Court + CLDF.               |
# +-------------------------------------------------------------+

## LEXENITH — Micro‑Court i CLDF (Cookbook)

### Generator pism (Motion)

curl -s -X POST http://127.0.0.1:8000/v1/lexenith/motion/generate \
  -H "Content-Type: application/json" \
  -d '{"case_id":"CER-LEX-001","pattern_id":"motion-dismiss","facts":{"a":1},"citations":["Art. 10", "Art. 22"]}'

### Renormalizacja cytowań (CLDF)

curl -s -X POST http://127.0.0.1:8000/v1/lexenith/cldf/renormalize \
  -H "Content-Type: application/json" \
  -d '{"citations":[{"text":"Art. 10","weight":1.0},{"text":"Art. 22","weight":2.0}],"damping":0.9}'

### Why‑Not (PCΔ) — eksport kontrargumentów

curl -s -X POST http://127.0.0.1:8000/v1/lexenith/why_not/export \
  -H "Content-Type: application/json" \
  -d '{"claim":"x","counter_arguments":["y","z"]}'

