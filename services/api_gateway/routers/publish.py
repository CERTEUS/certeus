# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/publish.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/publish.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""PL: Mapuje wynik rdzenia na kontrakt publikacji. EN: Map core to publication contract."""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from typing import Any

from fastapi import APIRouter, Header, HTTPException, Request

from core.truthops.engine import post_solve, pre_solve
from runtime.proof_queue import PROOF_QUEUE

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                          CERTEUS — HEART                            |

# +=====================================================================+

# | FILE: services/api_gateway/routers/publish.py                       |

# | ROLE:                                                               |

# |  PL: Publiczny endpoint publikacji (kontrakt Publication V1).       |

# |  EN: Public publication endpoint (Publication V1 contract).         |

# +=====================================================================+

router = APIRouter()

# === I/O / ENDPOINTS ===


@router.post("/defx/reason")
def reason(
    body: dict[str, Any],
    x_norm_pack_id: str = Header(..., alias="X-Norm-Pack-ID"),
    x_jurisdiction: str = Header(..., alias="X-Jurisdiction"),
    request: Request | None = None,
) -> dict[str, Any]:
    """PL: Zwraca status + PCO/plan/eta_hint. EN: Returns status + PCO/plan/eta_hint."""

    # PNIP validation (strict optional)
    try:
        from services.api_gateway.pnip import validate_pnip_request

        strict = (os.getenv("STRICT_PNIP") or "0").strip() in {"1", "true", "True"}
        if request is not None:
            _ = validate_pnip_request(request, body=body, strict=strict)
    except HTTPException as e:
        raise e
    except Exception:
        pass

    # Optional redaction on ingress before solve (W12 compliance)
    if (os.getenv("SEC_REDACTION_ENFORCED") or "0").strip() in {"1", "true", "True"}:
        try:
            from pathlib import Path
            import re

            import yaml

            pack = Path(__file__).resolve().parents[3] / "policies" / "pco" / "policy_pack.yaml"
            doc = yaml.safe_load(pack.read_text(encoding="utf-8")) or {}
            pats = [re.compile(str(p)) for p in (((doc.get("redaction") or {}).get("pii_patterns")) or [])]

            def _mask(v: Any) -> Any:
                if isinstance(v, dict):
                    return {k: _mask(x) for k, x in v.items()}
                if isinstance(v, list):
                    return [_mask(x) for x in v]
                if isinstance(v, str):
                    for rx in pats:
                        if rx.search(v):
                            return "[REDACTED]"
                return v

            body = _mask(body)
        except Exception:
            pass

    pre = pre_solve(body, policy_profile="default")

    if pre.heat != "HOT":
        task = PROOF_QUEUE.enqueue(
            tenant=body.get("tenant", "anon"), heat=pre.heat, payload=body, sla=body.get("sla", "basic")
        )

        return {
            "status": "PENDING",
            "proof_task_id": task.id,
            "eta_hint": task.eta_hint,
            "pco.plan": pre.plan,
            "headers": {"X-Norm-Pack-ID": x_norm_pack_id, "X-Jurisdiction": x_jurisdiction},
        }

    artifacts: dict[str, Any] = {}  # plug: wyniki z szybkich solverów

    decision, meta = post_solve(artifacts, policy_profile="default")

    resp: dict[str, Any] = {
        "status": decision,
        "headers": {"X-Norm-Pack-ID": x_norm_pack_id, "X-Jurisdiction": x_jurisdiction},
    }

    if decision == "PUBLISH":
        resp["pco"] = meta.get("pco", {})

    else:
        resp["pco.plan"] = meta.get("plan", {})

    return resp


# === TESTY / TESTS ===
