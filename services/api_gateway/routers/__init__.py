# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/__init__.py            |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/__init__.py            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Minimalne __init__, by uniknąć ostrzeżeń Pylance/Ruff o „unused import”.

EN: Minimal __init__ to avoid Pylance/Ruff 'unused import' warnings.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===


# [UWAGA]

# Nie re-eksportujemy tutaj verify/system/export/ledger, żeby nie generować

# F401/unused-import. Moduły importujemy bezpośrednio w main.py.
