# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/exporter_pl/src/main.py                     |

# | ROLE: Project module.                                       |

# | PLIK: plugins/exporter_pl/src/main.py                     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Wejście wtyczki exporter_pl (Domain Pack).

EN: exporter_pl plugin entry (Domain Pack).
"""

# === IMPORTY / IMPORTS ===

from services.exporter_service.exporter import export_answer

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/exporter_pl/src/main.py                     |

# | ROLE: Project module.                                       |

# | PLIK: plugins/exporter_pl/src/main.py                     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

def register(api):
    api.register_plugin("exporter_pl", {"version": "0.1.0"})

    # Register a concrete exporter that maps AnswerContract -> DOCX/PDF (stub uses exporter_service)

    api.register_exporter("pl.exporter.docx_pdf", export_answer)

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
