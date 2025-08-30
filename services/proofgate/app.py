from __future__ import annotations

from typing import Any

from fastapi import FastAPI
from pydantic import BaseModel, Field

app = FastAPI(title="ProofGate (stub)", version="0.2.0")


@app.get("/healthz")
def healthz() -> dict[str, Any]:
    return {"ok": True, "service": "proofgate-stub"}


class PublishRequest(BaseModel):
    pco: dict[str, Any] | None = Field(default=None, description="Proof-Carrying Object")
    policy: dict[str, Any] | None = None
    budget_tokens: int | None = None


class PublishResponse(BaseModel):
    status: str
    pco: dict[str, Any] | None = None
    ledger_ref: str | None = None


@app.post("/v1/proofgate/publish", response_model=PublishResponse)
def publish(req: PublishRequest) -> PublishResponse:
    """
    Stub publish endpoint as per manifest: returns one of
    PUBLISH|CONDITIONAL|PENDING|ABSTAIN with echo pco and optional ledger_ref.
    """
    if req.pco is None:
        # Without PCO we abstain (hardening happens in gateway layer in real setup)
        return PublishResponse(status="ABSTAIN", pco=None, ledger_ref=None)

    # Basic policy hint: if budget missing → PENDING
    if (req.budget_tokens or 0) <= 0:
        return PublishResponse(status="PENDING", pco=req.pco, ledger_ref=None)

    # Otherwise publish; ledger ref is a stub
    return PublishResponse(status="PUBLISH", pco=req.pco, ledger_ref="LEDGER-STUB-001")
