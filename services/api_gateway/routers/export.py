from fastapi import APIRouter

router = APIRouter()

@router.post("/export")
def export_endpoint(payload: dict):
    # stub: would call exporter_service
    return {"ok": True}
