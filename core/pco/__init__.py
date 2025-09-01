#!/usr/bin/env python3

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/pco/__init__.py                                |

# | ROLE: Project module.                                       |

# | PLIK: core/pco/__init__.py                                |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | PACKAGE / PAKIET: core/pco                                          |

# | DATE / DATA: 2025-08-19                                             |

# +=====================================================================+

# | EN: Core PCO utilities: canonical hashing, Merkle operations, and   |

# |     Ed25519 signing/verification for public, zero-PII evidence.     |

# | PL: Jądro PCO: kanoniczne hashowanie, operacje Merkle oraz           |

# |     podpis/weryfikacja Ed25519 dla publicznych dowodów 0 PII.       |

# +=====================================================================+

from __future__ import annotations

__all__ = [
    "b64u_encode",
    "b64u_decode",
    "sha256_hex",
    "canonical_bundle_hash_hex",
    "compute_leaf_hex",
    "canonical_digest_hex",
    "ed25519_sign_b64u",
    "ed25519_verify_b64u",
    "load_pubkey_bytes_from_env",
    "MerkleStep",
    "parse_merkle_proof",
    "apply_merkle_path",
    "PublicPCO",
]


from .crypto import (  # noqa: E402
    b64u_decode,
    b64u_encode,
    canonical_bundle_hash_hex,
    canonical_digest_hex,
    compute_leaf_hex,
    ed25519_sign_b64u,
    ed25519_verify_b64u,
    load_pubkey_bytes_from_env,
    sha256_hex,
)
from .merkle import (  # noqa: E402
    MerkleStep,
    apply_merkle_path,
    parse_merkle_proof,
)
from .public_payload import PublicPCO  # noqa: E402
