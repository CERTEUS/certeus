# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: core/truthops/engine.py                                       |
# | ROLE:                                                               |
# |  PL: Silnik TruthOps w dwóch fazach (pre/post) dla decyzji          |
# |      publikacji.                                                    |
# |  EN: Two-phase TruthOps engine (pre/post) for publication decisions.|
# +=====================================================================+

"""PL: Faza PRE: GoP/EUQ/TTDE (klasyfikacja HOT/WARM/COLD + plan).
POST: ATT/MTV (kontrtesty i spójność) → PUBLISH/CONDITIONAL/ABSTAIN.
EN:  PRE: GoP/EUQ/TTDE (HOT/WARM/COLD + plan). POST: ATT/MTV → verdict.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal

Decision = Literal["PUBLISH", "CONDITIONAL", "PENDING", "ABSTAIN"]
Heat = Literal["HOT", "WARM", "COLD"]


@dataclass(frozen=True)
class PreSolveResult:
    """PL: Wynik fazy PRE. EN: PRE phase result."""

    heat: Heat
    reasons: dict[str, Any]
    plan: dict[str, Any]  # initial plan-of-evidence for non-PUBLISH


def evaluate_gop(ctx: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    """PL: Ocena GoP. EN: GoP evaluation."""
    return {"ok": True, "sources": ctx.get("sources_count", 0)}


def evaluate_euq(ctx: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    """PL: Ocena EUQ (dolny przedział wiarygodności). EN: EUQ lower bound."""
    return {"lb": float(ctx.get("lb", 0.5))}


def evaluate_ttde(ctx: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    """PL: Datowanie/wygaśnięcie. EN: Temporal validity/expiry."""
    return {"fresh": bool(ctx.get("fresh", True))}


def classify_heat(
    gop: dict[str, Any],
    euq: dict[str, Any],
    ttde: dict[str, Any],
    policy: dict[str, Any],
) -> Heat:
    """PL: Reguła doboru HOT/WARM/COLD. EN: Heat classification rule."""
    lb = float(euq.get("lb", 0))
    fresh = bool(ttde.get("fresh", False))
    lower = float(policy["EUQ"]["lower_bound_publish"])
    band_lo = float(policy["EUQ"]["conditional_band"][0])
    if lb >= lower and fresh:
        return "HOT"
    if lb >= band_lo:
        return "WARM"
    return "COLD"


def pre_solve(ctx: dict[str, Any], policy_profile: str = "default") -> PreSolveResult:
    """PL: Wykonaj fazę PRE. EN: Execute PRE phase."""
    # Policy może być wstrzyknięte przez caller; zapewnij rozsądne domyślne.
    policy = ctx.get("truthops_policy", {}).get(policy_profile) or {
        "EUQ": {"lower_bound_publish": 0.75, "conditional_band": [0.55, 0.75]}
    }
    gop = evaluate_gop(ctx, policy)
    euq = evaluate_euq(ctx, policy)
    ttde = evaluate_ttde(ctx, policy)
    heat = classify_heat(gop, euq, ttde, policy)
    plan = {"summary": "Conditional proof plan", "steps": []}
    reasons = {"gop": gop, "euq": euq, "ttde": ttde}
    return PreSolveResult(heat=heat, reasons=reasons, plan=plan)


def evaluate_att(artifacts: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    """PL: Kontrprzykłady. EN: Adversarial tests."""
    # TODO: plug ATT results
    return {"passed": True, "missing_tests": []}


def evaluate_mtv(artifacts: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    """PL: Samospójność. EN: Meta-theoretic validity."""
    # TODO: plug MTV results
    return {"contradiction": False, "self_inconsistency": False}


def post_solve(
    artifacts: dict[str, Any],
    policy_profile: str = "default",
) -> tuple[Decision, dict[str, Any]]:
    """PL: Wykonaj fazę POST i zwróć decyzję. EN: Execute POST and return decision."""
    policy = {"ATT": {}, "MTV": {}}
    att = evaluate_att(artifacts, policy)
    mtv = evaluate_mtv(artifacts, policy)

    if mtv.get("contradiction") or mtv.get("self_inconsistency"):
        return "ABSTAIN", {"reason": "MTV rejection", "att": att, "mtv": mtv}

    if att.get("passed", False):
        return "PUBLISH", {"att": att, "mtv": mtv, "pco": artifacts.get("pco", {})}

    plan = {"summary": "Need additional tests/evidence", "steps": att.get("missing_tests", [])}
    return "CONDITIONAL", {"plan": plan, "att": att, "mtv": mtv}
