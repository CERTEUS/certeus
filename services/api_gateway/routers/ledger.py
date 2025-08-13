from fastapi import APIRouter

router = APIRouter()

@router.get("/ledger/health")
def health():
    return {"status": "ok"}
