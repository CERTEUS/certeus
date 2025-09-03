# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: examples/README.md                                  |
# | ROLE: Project Markdown.                                     |
# | PLIK: examples/README.md                                  |
# | ROLA: Przykłady użycia API (cURL/skrypty).                   |
# +-------------------------------------------------------------+

## Przykłady

- `fin_alpha_curl.sh` — szybki start Q‑Alpha (measure/simulate/pnl)
- `lex_motion_curl.sh` — Micro‑Court/CLDF/Why‑Not

Uruchom lokalnie serwer:

```
$py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
```

Potem wykonaj skrypty z katalogu `examples/`.

