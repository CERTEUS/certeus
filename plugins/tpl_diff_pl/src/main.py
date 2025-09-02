# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/tpl_diff_pl/src/main.py                     |

# | ROLE: Project module.                                       |

# | PLIK: plugins/tpl_diff_pl/src/main.py                     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""
PL: Wejście wtyczki tpl_diff_pl (Domain Pack).

EN: tpl_diff_pl plugin entry (Domain Pack).
"""

# === IMPORTY / IMPORTS ===
from datetime import datetime

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


# +-------------------------------------------------------------+


# |                          CERTEUS                            |


# +-------------------------------------------------------------+


# | FILE: plugins/tpl_diff_pl/src/main.py                     |


# | ROLE: Project module.                                       |


# | PLIK: plugins/tpl_diff_pl/src/main.py                     |


# | ROLA: Moduł projektu.                                       |


# +-------------------------------------------------------------+


def _mock_diff(act_id: str, v_from: str, v_to: str):
    # Placeholder: returns a deterministic "diff" shape

    return {
        "act_id": act_id,
        "from": v_from,
        "to": v_to,
        "changes": [
            {"type": "amend", "article": "art. 1", "note": "placeholder change"},
            {"type": "repeal", "article": "art. 2", "note": "placeholder repeal"},
        ],
        "generated_at": datetime.utcnow().isoformat() + "Z",
    }


def register(api):
    api.register_plugin("tpl_diff_pl", {"version": "0.1.0"})

    # Register as an adapter-like callable; convention: 'tpl.diff.pl'

    api.register_adapter("tpl.diff.pl", _mock_diff)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
