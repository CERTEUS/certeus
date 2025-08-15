# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/__init__.py              |
# | ROLE: Make 'routers' a package (no implicit re-exports).    |
# | PLIK: services/api_gateway/routers/__init__.py              |
# | ROLA: Czyni 'routers' pakietem (bez niejawnych re-eksportów).|
# +-------------------------------------------------------------+
"""
PL: Minimalne __init__, by uniknąć ostrzeżeń Pylance/Ruff o „unused import”.
EN: Minimal __init__ to avoid Pylance/Ruff 'unused import' warnings.
"""

# [UWAGA]
# Nie re-eksportujemy tutaj verify/system/export/ledger, żeby nie generować
# F401/unused-import. Moduły importujemy bezpośrednio w main.py.
