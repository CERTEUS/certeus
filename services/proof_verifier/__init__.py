"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/proof_verifier/__init__.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/proof_verifier/__init__.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from .verifier import verify_drat, verify_lfsc

__all__ = ["verify_lfsc", "verify_drat"]
