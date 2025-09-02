# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_lexlog.py                       |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_lexlog.py                       |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Testuje minimalny parser LEXLOG na pliku kk.lex.

EN: Tests the minimal LEXLOG parser on kk.lex file.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from pathlib import Path

from services.lexlog_parser.parser import parse_lexlog


def test_lexlog_parser_kk_lex() -> None:
    lex_path = Path("packs") / "jurisdictions" / "PL" / "rules" / "kk.lex"

    assert lex_path.exists(), "Missing packs/jurisdictions/PL/rules/kk.lex"

    content = lex_path.read_text(encoding="utf-8")

    ast = parse_lexlog(content)

    # Defines present

    names = {d.name for d in ast.defines}

    assert {
        "cel_korzysci_majatkowej",
        "wprowadzenie_w_blad",
        "niekorzystne_rozporzadzenie_mieniem",
    }.issubset(names)

    # Premises present

    pids = {p.id for p in ast.premises}

    assert {"P_CEL", "P_WPROWADZENIE", "P_ROZPORZADZENIE"}.issubset(pids)

    # Rule ties premises to conclusion

    rule = next(r for r in ast.rules if r.id == "R_286_OSZUSTWO")

    assert rule.conclusion == "K_OSZUSTWO_STWIERDZONE"

    assert set(rule.premises) == {"P_CEL", "P_WPROWADZENIE", "P_ROZPORZADZENIE"}

    # Conclusion has assertion

    concl = next(c for c in ast.conclusions if c.id == "K_OSZUSTWO_STWIERDZONE")

    assert concl.assert_expr is not None and "cel_korzysci_majatkowej" in concl.assert_expr
