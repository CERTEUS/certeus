# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/plugins/tpl_diff_pl/src/main.py         |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/tpl_diff_pl/src/main.py                     |

# | ROLE: Project module.                                       |

# | PLIK: plugins/tpl_diff_pl/src/main.py                     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""



PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.



EN: CERTEUS module – please complete the functional description.



"""


# +-------------------------------------------------------------+


# |                          CERTEUS                            |


# +-------------------------------------------------------------+


# | FILE: plugins/tpl_diff_pl/src/main.py                     |


# | ROLE: Project module.                                       |


# | PLIK: plugins/tpl_diff_pl/src/main.py                     |


# | ROLA: Moduł projektu.                                       |


# +-------------------------------------------------------------+

from datetime import datetime


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
