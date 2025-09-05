#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_domains.py                   |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_domains.py                   |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy domenowego lensingu CFE: różne mapy dla MED/SEC/CODE/FIN/LEX
    oraz granice wartości [0,1] i klucze charakterystyczne.

EN: CFE domain lensing tests: distinct maps for MED/SEC/CODE/FIN/LEX,
    value bounds [0,1], and presence of characteristic keys.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient


def _get(client: TestClient, domain: str | None) -> dict:
    q = "" if not domain else f"?domain={domain}"
    r = client.get(f"/v1/cfe/lensing{q}")
    assert r.status_code == 200
    return r.json()


def test_lensing_default_lex_like() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    js = _get(c, None)
    lm = js.get("lensing_map", {})
    assert "precedent:K_2001" in lm
    assert all(0.0 <= float(v) <= 1.0 for v in lm.values())


def test_lensing_med_sec_code_fin_domains() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    med = _get(c, "med")
    sec = _get(c, "SEC")
    code = _get(c, "Code")
    fin = _get(c, "fin")

    assert "icd10:I21" in med.get("lensing_map", {})
    assert "nist:SP800-53:AC-2" in sec.get("lensing_map", {})
    assert "cwe:79" in code.get("lensing_map", {})
    assert "reg:MiFID2:best_execution" in fin.get("lensing_map", {})

    # Bounds for all
    for js in (med, sec, code, fin):
        for v in js.get("lensing_map", {}).values():
            fv = float(v)
            assert 0.0 <= fv <= 1.0


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
