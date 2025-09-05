# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: clients/cli/certeus_cli.py                          |

# | ROLE: Project module.                                       |

# | PLIK: clients/cli/certeus_cli.py                          |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Prosta linia poleceń dla CERTEUS.
    - `version` – wypisz wersję.
    - `openapi` – wygeneruj OpenAPI do `out/openapi.json`.
    - `endpoints` – wypisz zebrane endpointy (metoda, ścieżka, nazwa).

EN: Simple CLI for CERTEUS.
    - `version` – print version.
    - `openapi` – generate OpenAPI JSON to `out/openapi.json`.
    - `endpoints` – list endpoints (method, path, name).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

# Ensure repo root on sys.path for script execution
REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))  # noqa: E402

from core.version import __version__  # noqa: E402
from services.api_gateway.main import app  # noqa: E402

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: clients/cli/certeus_cli.py                          |

# | ROLE: Project module.                                       |

# | PLIK: clients/cli/certeus_cli.py                          |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

def _cmd_version(_: argparse.Namespace) -> int:
    print(__version__)
    return 0

def _cmd_openapi(args: argparse.Namespace) -> int:
    out_dir = REPO_ROOT / "out"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_file = out_dir / "openapi.json"
    spec = app.openapi()
    out_file.write_text(json.dumps(spec, ensure_ascii=False, indent=2), encoding="utf-8")
    if args.print:
        print(out_file)
    return 0

def _cmd_endpoints(_: argparse.Namespace) -> int:
    for route in app.routes:
        methods = getattr(route, "methods", None)
        path = getattr(route, "path", None)
        name = getattr(route, "name", None)
        if methods and path:
            for m in sorted(methods):
                print(f"{m:6s} {path} {name or ''}".rstrip())
    return 0

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="certeus", description="CERTEUS CLI")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_ver = sub.add_parser("version", help="print version")
    p_ver.set_defaults(func=_cmd_version)

    p_open = sub.add_parser("openapi", help="generate OpenAPI JSON")
    p_open.add_argument("--print", action="store_true", help="print written file path")
    p_open.set_defaults(func=_cmd_openapi)

    p_ls = sub.add_parser("endpoints", help="list API endpoints")
    p_ls.set_defaults(func=_cmd_endpoints)

    args = parser.parse_args(argv)
    return int(args.func(args))

if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
