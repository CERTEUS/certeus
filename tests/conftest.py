# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/conftest.py                                   |

# | ROLE: Project module.                                       |

# | PLIK: tests/conftest.py                                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/tests/conftest.py                       |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/conftest.py                                     |

# | ROLE: Shared pytest fixtures & test helpers.                |

# | PLIK: tests/conftest.py                                     |

# | ROLA: Wspólne fikstury pytest i pomocniki testowe.          |

# +-------------------------------------------------------------+

"""

PL: Zbiór współdzielonych fikstur i pomocników testowych dla całego pakietu testów.

EN: Shared pytest fixtures and helpers used across the test suite.

"""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
