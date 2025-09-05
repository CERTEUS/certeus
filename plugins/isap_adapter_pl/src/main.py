# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/isap_adapter_pl/src/main.py                 |

# | ROLE: Project module.                                       |

# | PLIK: plugins/isap_adapter_pl/src/main.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Wejście wtyczki isap_adapter_pl (Domain Pack).

EN: isap_adapter_pl plugin entry (Domain Pack).
"""

# === IMPORTY / IMPORTS ===

from services.sipp_indexer_service.index_isap import snapshot_pl

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/isap_adapter_pl/src/main.py                 |

# | ROLE: Project module.                                       |

# | PLIK: plugins/isap_adapter_pl/src/main.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

def register(api):
    api.register_plugin("isap_adapter_pl", {"version": "0.1.0"})

    # Adapter for ISAP snapshots with hash+timestamp persistence

    api.register_adapter("isap.pl.snapshot", snapshot_pl)

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
