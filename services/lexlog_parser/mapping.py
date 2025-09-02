# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/lexlog_parser/mapping.py                   |

# | ROLE: Project module.                                       |

# | PLIK: services/lexlog_parser/mapping.py                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Loader mapowania LEXLOG -> engine flags. JSON w repo trzymamy w packs/... .

EN: Loader of LEXLOG -> engine flags mapping. JSON lives in packs/... .

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path

from pydantic import BaseModel, Field

from services.lexlog_parser.evaluator import EvalContext

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===
class _MappingModel(BaseModel):
    premise_to_flag: dict[str, str | None] = Field(default_factory=dict)

    conclusion_excludes: dict[str, list[str]] = Field(default_factory=dict)


# === LOGIKA / LOGIC ===


def load_mapping(path: Path) -> EvalContext:
    """

    PL: Wczytuje plik JSON i zwraca EvalContext (puste/null pomija).

    EN: Loads JSON and returns EvalContext (skips empty/null).

    """

    data = json.loads(path.read_text(encoding="utf-8"))

    model = _MappingModel.model_validate(data)

    cleaned: dict[str, str] = {k: v for k, v in model.premise_to_flag.items() if v}

    return EvalContext(premise_to_flag=cleaned, conclusion_excludes=model.conclusion_excludes)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
