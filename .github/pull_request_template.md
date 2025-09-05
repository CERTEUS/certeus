# +-------------------------------------------------------------+

# | CERTEUS |

# +-------------------------------------------------------------+

# | FILE: .github/PULL_REQUEST_TEMPLATE.md |

# | ROLE: Project Markdown. |

# | PLIK: .github/PULL_REQUEST_TEMPLATE.md |

# | ROLA: Dokument Markdown. |

# +-------------------------------------------------------------+

## Opis zmian / Summary

- [ ] Krótki opis co i dlaczego

## Checklist (CI Gates / Proof-Only)

- [ ] Gauge-Gate (holonomy) zielony
- [ ] Path-Coverage-Gate (γ ≥ 0.90, uncaptured ≤ 0.05) zielony
- [ ] Boundary-Rebuild-Gate (delta_bits == 0) zielony
- [ ] Proof-Only I/O: publikowalne wyniki zawierają PCO

## Dodatkowo

- [ ] Lint (ruff) i testy (pytest) zielone
- [ ] Premium Style (sec.21) OK (banery/docstringi/sekcje)
