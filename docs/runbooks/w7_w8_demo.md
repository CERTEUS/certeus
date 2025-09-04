#!/usr/bin/env markdown

# CERTEUS — Runbook: W7/W8 Demo

## W7 — FINENITH v0.1

- Pomiar (R/S + polityka):
  - `POST /v1/fin/alpha/measure` z `signals` → nagłówek `X-CERTEUS-Policy-FIN` (policy_ok/violations).
- Komutator R/S:
  - `POST /v1/fin/alpha/operators_rs` → `commutator_norm` oraz metryki.
- MI (splątanie aktywów):
  - `POST /v1/fin/alpha/entanglement/mi` z parą serii czasowych.
- PnL i sandbox:
  - `POST /v1/fin/alpha/simulate` (dwie strategie), `GET /v1/fin/alpha/pnl`.
  - Paper: `/paper/open`, `/paper/order`, `/paper/positions`, `/paper/equity`.

## W8 — LEXENITH v0.1

- Motion generator:
  - `POST /v1/lexenith/motion/generate` (PCO cytatów z hash/uri).
- CLDF renormalize:
  - `POST /v1/lexenith/cldf/renormalize` (authority_score, normalized=true).
- Why‑Not / PCΔ:
  - `POST /v1/lexenith/why_not/export` → `trace_uri` (pfs://why-not/...).
- Micro‑Court (lock→publish):
  - `POST /v1/lexenith/micro_court/lock` → nagłówek PCO,
  - `POST /v1/lexenith/micro_court/publish` → path + zapis do Ledger.
- DR lock/revoke:
  - `POST /v1/dr/lock`, `POST /v1/dr/revoke` (horyzont w sprawach).

## Skrypty demo

- `python scripts/demos/run_w8_demo.py` → `reports/w8_demo.json`: motion → CLDF → Why-Not → Micro‑Court → DR.

