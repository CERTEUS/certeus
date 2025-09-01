# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: utils/__init__.py                                   |

# | ROLE: Project module.                                       |

# | PLIK: utils/__init__.py                                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/utils/__init__.py                       |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: utils/__init__.py                                     |

# | ROLE: Utils package public surface.                         |

# | PLIK: utils/__init__.py                                     |

# | ROLA: Publiczny interfejs pakietu utils.                    |

# +-------------------------------------------------------------+

"""

PL: Inicjalizacja pakietu narzędziowego; eksportuje najczęściej używane helpery.

EN: Package initializer for utilities; exports commonly used helpers.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===


from .console import ascii_safe, error, info, print_safe, success  # noqa: F401

__all__ = ["ascii_safe", "print_safe", "info", "success", "error"]
