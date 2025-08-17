#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/exporter_service/__init__.py   |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/exporter_service/__init|
# | DATE:    2025-08-17                                          |
# +=====================================================================+
"""
PL: Pakiet inicjalizacyjny modułu.
EN: Package initializer.
"""

# -*- coding: utf-8 -*-
# +=====================================================================+
# |                              CERTEUS                                |
# |                     Exporter Service Package                        |
# +=====================================================================+
# | MODULE:  services/exporter_service/__init__.py                      |
# | VERSION: 1.0.2                                                      |
# | DATE:    2025-08-16                                                 |
# +=====================================================================+
# | ROLE: Public API re-exports                                         |
# +=====================================================================+

from __future__ import annotations

from .exporter import ExporterService, export_answer_to_txt, export_answer

__all__ = ["ExporterService", "export_answer_to_txt", "export_answer"]
