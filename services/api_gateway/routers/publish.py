"""PL: Mapuje wynik rdzenia na kontrakt publikacji. EN: Map core to publication contract."""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from typing import Any

from fastapi import APIRouter, Header

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
# === I/O / ENDPOINTS ===
def reason(
    body: dict[str, Any],
    x_norm_pack_id: str = Header(..., alias="X-Norm-Pack-ID"),
    x_jurisdiction: str = Header(..., alias="X-Jurisdiction"),
) -> dict[str, Any]:
    """PL: Zwraca status + PCO/plan/eta_hint. EN: Returns status + PCO/plan/eta_hint."""
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
