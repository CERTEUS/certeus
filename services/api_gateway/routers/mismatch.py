from fastapi import APIRouter

router = APIRouter()


@router.get("/mismatch")
def list_mismatch():
    # stub
    return {"items": []}
