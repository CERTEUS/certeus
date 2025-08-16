# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |      Core Engine for Reliable & Unified Systems             |
# +-------------------------------------------------------------+
# | FILE: services/lexlog_parser/mapping.py                     |
# | ROLE: Load LEXLOG↔engine mapping from JSON into EvalContext |
# +-------------------------------------------------------------+

"""
PL: Loader mapowania LEXLOG -> engine flags. JSON w repo trzymamy w packs/... .
EN: Loader of LEXLOG -> engine flags mapping. JSON lives in packs/... .
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List, Optional

from pydantic import BaseModel, Field

from services.lexlog_parser.evaluator import EvalContext


class _MappingModel(BaseModel):
    premise_to_flag: Dict[str, Optional[str]] = Field(default_factory=dict)
    conclusion_excludes: Dict[str, List[str]] = Field(default_factory=dict)


def load_mapping(path: Path) -> EvalContext:
    """
    PL: Wczytuje plik JSON i zwraca EvalContext (puste/null pomija).
    EN: Loads JSON and returns EvalContext (skips empty/null).
    """
    data = json.loads(path.read_text(encoding="utf-8"))
    model = _MappingModel.model_validate(data)
    cleaned: Dict[str, str] = {k: v for k, v in model.premise_to_flag.items() if v}
    return EvalContext(
        premise_to_flag=cleaned, conclusion_excludes=model.conclusion_excludes
    )
