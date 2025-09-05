#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/cfe_config.py           |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/cfe_config.py           |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Konfiguracja CFE (stubs): mapy lensingu per domena oraz progi
    heurystyk lock dla horyzontu.

EN: CFE configuration (stubs): domain-specific lensing maps and
    lock heuristics thresholds for horizon.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

# === KONFIGURACJA / CONFIGURATION ===

# Domenowe mapy lensingu: klucze → wagi [0,1]
LENSING_WEIGHTS: dict[str, dict[str, float]] = {
    "LEX": {"precedent:K_2001": 0.42, "precedent:III_2020": 0.28},
    "FIN": {"reg:MiFID2:best_execution": 0.31, "esma:guidelines": 0.24},
    "MED": {"icd10:I21": 0.37, "icd10:E11": 0.22, "loinc:718-7": 0.18},
    "SEC": {"nist:SP800-53:AC-2": 0.33, "iso27001:A.12": 0.26, "cwe:79": 0.19},
    "CODE": {"cwe:79": 0.35, "owasp:top10:a03": 0.27, "rfc:9110": 0.14},
}

# Domeny i poziomy, które implikują lock horyzontu (heurystyka)
DOMAINS_LOCK = {"MED", "SEC", "CODE", "FIN"}
SEVERITY_LOCK = {"high", "critical"}


def get_lensing_map(domain: str | None) -> tuple[dict[str, float], list[str], str]:
    """Zwraca (mapa_wag, krytyczne_klucze, domena_norm).

    - domain: wejściowa nazwa domeny (None → LEX)
    - krytyczne_klucze: heurystycznie — najwyższy wagowo element
    """

    d = (domain or "LEX").strip().upper()
    weights = LENSING_WEIGHTS.get(d) or LENSING_WEIGHTS["LEX"]
    # Clamp i kopia
    clamped = {k: float(max(0.0, min(1.0, v))) for k, v in weights.items()}
    # Krytyczny: max po wadze (deterministycznie)
    if clamped:
        max_key = max(clamped.items(), key=lambda kv: (kv[1], kv[0]))[0]
        crit = [max_key]
    else:
        crit = []
    return clamped, crit, d


# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
