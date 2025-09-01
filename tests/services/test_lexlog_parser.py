# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_lexlog_parser.py                |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_lexlog_parser.py                |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/tests/services/test_lexlog_parser.py    |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_lexlog_parser.py                  |

# | ROLE: Unit tests for LEXLOG parser AST & legacy stub        |

# | PLIK: tests/services/test_lexlog_parser.py                  |

# | ROLA: Testy parsera LEXLOG (AST i zgodność legacy)          |

# +-------------------------------------------------------------+


"""

CERTEUS — LEXLOG Parser Tests

PL: Testy sprawdzające parsowanie: DEFINE/PREMISE/RULE/CONCLUSION,

    normalizację ID oraz zgodność z legacy stubem.

EN: Tests for parsing of DEFINE/PREMISE/RULE/CONCLUSION, canonical ID

    normalization, and legacy stub compatibility.

"""

from pathlib import Path

from services.lexlog_parser.parser import LexlogParser

RULES = Path("packs/jurisdictions/PL/rules/kk.lex")


def test_lexlog_parses_art_286_rule():
    text = RULES.read_text(encoding="utf-8")

    ast = LexlogParser().parse(text)

    assert ast, "AST should not be empty"

    assert ast["rule_id"] == "R_286_OSZUSTWO"

    assert ast["conclusion"] == "K_OSZUSTWO_STWIERDZONE"

    assert set(ast["premises"]) == {"P_CEL", "P_WPROWADZENIE", "P_ROZPORZADZENIE"}

    assert "z3.And(" in ast["smt_assertion"]
