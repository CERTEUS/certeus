
# Goal

PL: Prosty, tekstowy DSL do formalizacji reguł prawa (czytelny, diff-friendly).  
EN: Simple, text-based DSL to formalize legal rules (readable, diff-friendly).

## Core constructs (MVP)

- `DEFINE <name>: <Type>`
- `PREMISE <ID>: "<human label>"`
  - Optional detail lines, e.g. `EXISTS (...)`, `MAPS_TO (...)` (ignored by MVP parser)
- `RULE <ID> (P1, P2, ...) -> K1`
- `CONCLUSION <ID>: "<human label>"`
  - Optional `ASSERT (<expr>)`

Comments start with `#`. ASCII preferowane w plikach reguł (CLI/logi Windows).

## Example (KK-286)

DEFINE cel_korzysci_majatkowej: Bool
DEFINE wprowadzenie_w_blad: Bool
DEFINE niekorzystne_rozporzadzenie_mieniem: Bool

PREMISE P_CEL: "Cel osiagniecia korzysci majatkowej"
PREMISE P_WPROWADZENIE: "Wprowadzenie w blad"
PREMISE P_ROZPORZADZENIE: "Niekorzystne rozporzadzenie mieniem"

RULE R_286 (P_CEL, P_WPROWADZENIE, P_ROZPORZADZENIE) -> K_286

CONCLUSION K_286: "Znamiona oszustwa z art. 286 k.k."
ASSERT (cel_korzysci_majatkowej AND wprowadzenie_w_blad AND niekorzystne_rozporzadzenie_mieniem)

## AST (MVP)

```json
{
  "defines": [{"name":"...", "type":"..."}],
  "premises": [{"id":"P_...", "label":"..."}],
  "rules": [{"id":"R_...", "premises":["P_..."], "conclusion":"K_..."}],
  "conclusions": [{"id":"K_...", "label":"...", "assert_expr":"..."}]
}
---

## 2) `packs/jurisdictions/PL/rules/kk.lex`
