#!/usr/bin/env python3
# +-------------------------------------------------------------+
# | CERTEUS Control System | ForgeHeader v3 - Enterprise     |
# | FILE: workspaces/certeus/services/lexlog_parser/mapping.py                                      |
# | ROLE: Data mapping utilities                                        |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def load_mapping(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))
