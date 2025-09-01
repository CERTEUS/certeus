# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/isap_adapter_pl/src/main.py                 |

# | ROLE: Project module.                                       |

# | PLIK: plugins/isap_adapter_pl/src/main.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""







PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.







EN: CERTEUS module – please complete the functional description.







"""


# +-------------------------------------------------------------+


# |                          CERTEUS                            |


# +-------------------------------------------------------------+


# | FILE: plugins/isap_adapter_pl/src/main.py                 |


# | ROLE: Project module.                                       |


# | PLIK: plugins/isap_adapter_pl/src/main.py                 |


# | ROLA: Moduł projektu.                                       |


# +-------------------------------------------------------------+

from services.sipp_indexer_service.index_isap import snapshot_pl


def register(api):
    api.register_plugin("isap_adapter_pl", {"version": "0.1.0"})

    # Adapter for ISAP snapshots with hash+timestamp persistence

    api.register_adapter("isap.pl.snapshot", snapshot_pl)
