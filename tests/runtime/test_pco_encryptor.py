# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/runtime/test_pco_encryptor.py                 |

# | ROLE: Project module.                                       |

# | PLIK: tests/runtime/test_pco_encryptor.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE / PLIK: tests/runtime/test_pco_encryptor.py                    |

# | ROLE / ROLA:                                                         |

# |  EN: Unit tests for PCO envelope encryption (AES-GCM).              |

# |  PL: Testy jednostkowe szyfrowania kopertowego PCO (AES-GCM).       |

# +=====================================================================+

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from cryptography.exceptions import InvalidTag
import pytest

from runtime.pco_encryptor import decrypt, encrypt, new_dek

def test_round_trip_no_aad() -> None:
    """

    EN: Basic round-trip without AAD must restore plaintext.

    PL: Podstawowy round-trip bez AAD ma odtworzyć plaintext.

    """

    dek = new_dek()

    iv, ct, aad = encrypt(dek, b"lorem", b"")

    assert decrypt(dek, iv, ct, aad) == b"lorem"

def test_round_trip_with_aad() -> None:
    """

    EN: Round-trip with AAD must restore plaintext when AAD matches.

    PL: Round-trip z AAD ma odtworzyć plaintext przy zgodnym AAD.

    """

    dek = new_dek()

    aad = b"case:demo-001"

    iv, ct, _ = encrypt(dek, b"ipsum", aad)

    assert decrypt(dek, iv, ct, aad) == b"ipsum"

def test_wrong_aad_raises_invalid_tag() -> None:
    """

    EN: Decryption with wrong AAD must fail with InvalidTag.

    PL: Odszyfrowanie z błędnym AAD ma zwrócić błąd InvalidTag.

    """

    dek = new_dek()

    iv, ct, _ = encrypt(dek, b"secret", b"good-aad")

    with pytest.raises(InvalidTag):
        _ = decrypt(dek, iv, ct, b"bad-aad")
