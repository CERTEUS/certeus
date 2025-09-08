```
# +=============================================================+
# |                        CERTEUS — DOC                        |
# +=============================================================+
# | FILE: certeus/policies/VERSIONING.md                        |
# | TYPE: Versioning Policy (PCO & Policies)                    |
# | FORGEHEADER: v2                                             |
# | UPDATED: 2025-09-08Z                                        |
# +=============================================================+
```

# Polityka wersjonowania (PCO i polityki)

Cel: zapewnić kompatybilność i kontrolę zmian w PCO/politykach.

## Zasady (SemVer‑like dla kontraktów)
- MAJOR — zmiany niekompatybilne (usunięcia/pola obowiązkowe/semantyka)
- MINOR — zmiany kompatybilne (nowe pola opcjonalne/rozszerzenia)
- PATCH — poprawki bez wpływu na semantykę

## PCO
- Wersja schema w polu `pco_version` (np. `0.3.x`).
- Zasada: `additionalProperties: false` (ścisła walidacja); nowe pola → MINOR.
- Pola kryptograficzne (`inputs_digest`, `outputs_digest`, `model_fingerprint`) — zmiany → MINOR/MAJOR wg wpływu.

## Polityki (OPA/Rego, Gate’y)
- Wersja polityki w nagłówku (np. `policy_version: 0.1.0`).
- Zmiana reguł egzekwujących → MINOR/MAJOR.
- Tryb report‑only vs enforce opisany w changelogu.

## Procedura zmiany
1. ADR dla zmiany istotnej.
2. Aktualizacja wersji i changelog.
3. Testy kontraktu (schemathesis / JSON Schema) + ci‑gates PASS.

