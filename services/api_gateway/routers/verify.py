from fastapi import APIRouter
from kernel.truth_engine import verify

router = APIRouter()


@router.post("/verify")
def verify_endpoint(payload: dict):
    assumptions = payload.get("assumptions", [])
    return verify(assumptions)
