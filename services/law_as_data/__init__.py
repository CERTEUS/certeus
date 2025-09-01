"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/law_as_data/__init__.py                    |

# | ROLE: Project module.                                       |

# | PLIK: services/law_as_data/__init__.py                    |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from .cache import FileCache, cache_from_uri, compute_digest

__all__ = [
    "FileCache",
    "cache_from_uri",
    "compute_digest",
]
