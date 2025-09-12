#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: routers/ledger.py                                    |
# | ROLE: A2 - Ledger API Integration & Endpoints             |
# | PLIK: routers/ledger.py                                    |
# | ROLA: A2 - Ledger API Integration & Endpoints             |
# +-------------------------------------------------------------+

"""
PL: Router dla A2 Ledger - API endpoints dla systemu księgi rozrachunkowej
EN: A2 Ledger Router - API endpoints for the ledger system

Endpoints:
- POST /ledger/cases - Create new case
- GET /ledger/cases/{case_id} - Get case details
- POST /ledger/events - Record new event
- GET /ledger/events/{event_id} - Get event details
- GET /ledger/chain/integrity - Verify chain integrity
- POST /ledger/bundles - Store bundle
- GET /ledger/bundles/{bundle_id} - Get bundle
- GET /ledger/health - Health check
- GET /ledger/metrics - Performance metrics
"""

from datetime import datetime
from typing import Any
from uuid import UUID

from fastapi import APIRouter, BackgroundTasks, Depends, HTTPException, Query
from fastapi.responses import StreamingResponse
from pydantic import BaseModel, Field, validator

from core.auth import get_current_user, require_permissions
from core.logging import get_logger
from services.ledger_service.postgres_ledger import LedgerConfig, PostgreSQLLedger

# === MODELS ===

class CreateCaseRequest(BaseModel):
    """Request model for creating a new case"""
    case_id: str = Field(..., description="Unique case identifier")
    jurisdiction: dict[str, Any] = Field(..., description="Case jurisdiction details")
    metadata: dict[str, Any] | None = Field(default=None, description="Additional case metadata")

    @validator("case_id")
    def validate_case_id(cls, v):
        if not v or len(v) < 3:
            raise ValueError("Case ID must be at least 3 characters")
        if not v.replace("-", "").replace("_", "").isalnum():
            raise ValueError("Case ID must be alphanumeric with optional dashes/underscores")
        return v

class CreateCaseResponse(BaseModel):
    """Response model for case creation"""
    case_id: str
    created_at: datetime
    jurisdiction: dict[str, Any]
    metadata: dict[str, Any] | None
    chain_position: int

class RecordEventRequest(BaseModel):
    """Request model for recording an event"""
    event_type: str = Field(..., description="Type of event being recorded")
    case_id: str = Field(..., description="Associated case ID")
    payload: dict[str, Any] = Field(..., description="Event payload data")
    actor: str | None = Field(default=None, description="Actor performing the event")
    correlation_id: str | None = Field(default=None, description="Correlation ID for tracing")

    @validator("event_type")
    def validate_event_type(cls, v):
        if not v or len(v) < 2:
            raise ValueError("Event type must be at least 2 characters")
        return v.upper()

class RecordEventResponse(BaseModel):
    """Response model for event recording"""
    event_id: UUID
    event_type: str
    case_id: str
    recorded_at: datetime
    chain_position: int
    chain_hash: str
    tsa_timestamp: str | None

class StoreBundleRequest(BaseModel):
    """Request model for storing a bundle"""
    bundle_id: str = Field(..., description="Unique bundle identifier")
    case_id: str = Field(..., description="Associated case ID")
    bundle_data: bytes = Field(..., description="Bundle data")
    signature_ed25519: str = Field(..., description="Ed25519 signature")
    public_key_id: str = Field(..., description="Public key identifier")

class StoreBundleResponse(BaseModel):
    """Response model for bundle storage"""
    bundle_id: str
    case_id: str
    stored_at: datetime
    bundle_hash: str
    storage_location: str
    size_bytes: int

class ChainIntegrityResponse(BaseModel):
    """Response model for chain integrity verification"""
    is_valid: bool
    total_events: int
    verification_time: float
    chain_breaks: list[dict[str, Any]]
    merkle_anchors_verified: int
    last_verified_position: int

class LedgerHealthResponse(BaseModel):
    """Response model for ledger health check"""
    status: str
    database_status: str
    storage_status: str
    tsa_status: str
    chain_status: str
    performance_metrics: dict[str, Any]
    timestamp: datetime

class LedgerMetricsResponse(BaseModel):
    """Response model for ledger metrics"""
    events_per_second: float
    total_events: int
    total_cases: int
    total_bundles: int
    average_latency_ms: float
    chain_length: int
    storage_usage_mb: float
    timestamp: datetime

# === DEPENDENCIES ===

async def get_ledger() -> PostgreSQLLedger:
    """Get ledger instance"""
    config = LedgerConfig.from_env()
    ledger = PostgreSQLLedger(config)
    await ledger.initialize()
    return ledger

# === ROUTER ===

router = APIRouter(prefix="/ledger", tags=["A2 - Ledger"])
logger = get_logger("ledger_router")

@router.post("/cases", response_model=CreateCaseResponse)
async def create_case(
    request: CreateCaseRequest,
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:write"]))
):
    """
    Create a new case in the ledger

    This endpoint creates a new case entry in the ledger system.
    Each case represents a distinct legal or business process that
    will have associated events recorded against it.
    """
    try:
        logger.info(f"Creating case {request.case_id} for user {current_user.get('username', 'unknown')}")

        # Create case
        case_record = await ledger.create_case(
            case_id=request.case_id,
            jurisdiction=request.jurisdiction,
            metadata=request.metadata or {}
        )

        logger.info(f"Case {request.case_id} created successfully at position {case_record.chain_position}")

        return CreateCaseResponse(
            case_id=case_record.case_id,
            created_at=case_record.created_at,
            jurisdiction=case_record.jurisdiction,
            metadata=case_record.metadata,
            chain_position=case_record.chain_position
        )

    except ValueError as e:
        logger.warning(f"Invalid case creation request: {str(e)}")
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        logger.error(f"Failed to create case {request.case_id}: {str(e)}")
        raise HTTPException(status_code=500, detail="Internal server error")

@router.get("/cases/{case_id}")
async def get_case(
    case_id: str,
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:read"]))
):
    """
    Get case details by case ID

    Retrieves detailed information about a specific case,
    including its jurisdiction, metadata, and creation details.
    """
    try:
        case_record = await ledger.get_case(case_id)

        if not case_record:
            raise HTTPException(status_code=404, detail=f"Case {case_id} not found")

        return {
            "case_id": case_record.case_id,
            "created_at": case_record.created_at,
            "jurisdiction": case_record.jurisdiction,
            "metadata": case_record.metadata,
            "chain_position": case_record.chain_position,
            "event_count": await ledger.get_case_event_count(case_id)
        }

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Failed to get case {case_id}: {str(e)}")
        raise HTTPException(status_code=500, detail="Internal server error")

@router.post("/events", response_model=RecordEventResponse)
async def record_event(
    request: RecordEventRequest,
    background_tasks: BackgroundTasks,
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:write"]))
):
    """
    Record a new event in the ledger

    Records a new event against an existing case. Events are
    immutably stored in the chain with cryptographic integrity.
    """
    try:
        logger.info(f"Recording {request.event_type} event for case {request.case_id}")

        # Record event
        event_record = await ledger.record_event(
            event_type=request.event_type,
            case_id=request.case_id,
            payload=request.payload,
            actor=request.actor or current_user.get('username', 'unknown'),
            correlation_id=request.correlation_id
        )

        # Schedule background chain integrity check if needed
        background_tasks.add_task(_schedule_integrity_check, ledger, event_record.chain_position)

        logger.info(f"Event {event_record.event_id} recorded at position {event_record.chain_position}")

        return RecordEventResponse(
            event_id=event_record.event_id,
            event_type=event_record.event_type,
            case_id=event_record.case_id,
            recorded_at=event_record.recorded_at,
            chain_position=event_record.chain_position,
            chain_hash=event_record.chain_hash,
            tsa_timestamp=event_record.tsa_timestamp
        )

    except ValueError as e:
        logger.warning(f"Invalid event recording request: {str(e)}")
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        logger.error(f"Failed to record event: {str(e)}")
        raise HTTPException(status_code=500, detail="Internal server error")

@router.get("/events/{event_id}")
async def get_event(
    event_id: UUID,
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:read"]))
):
    """
    Get event details by event ID

    Retrieves detailed information about a specific event,
    including its payload, chain position, and integrity data.
    """
    try:
        event_record = await ledger.get_event(event_id)

        if not event_record:
            raise HTTPException(status_code=404, detail=f"Event {event_id} not found")

        return {
            "event_id": event_record.event_id,
            "event_type": event_record.event_type,
            "case_id": event_record.case_id,
            "payload": event_record.payload,
            "actor": event_record.actor,
            "recorded_at": event_record.recorded_at,
            "chain_position": event_record.chain_position,
            "chain_hash": event_record.chain_hash,
            "previous_hash": event_record.previous_hash,
            "tsa_timestamp": event_record.tsa_timestamp,
            "correlation_id": event_record.correlation_id
        }

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Failed to get event {event_id}: {str(e)}")
        raise HTTPException(status_code=500, detail="Internal server error")

@router.get("/chain/integrity", response_model=ChainIntegrityResponse)
async def verify_chain_integrity(
    from_position: int | None = Query(None, description="Start verification from this position"),
    to_position: int | None = Query(None, description="End verification at this position"),
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:verify"]))
):
    """
    Verify chain integrity

    Performs cryptographic verification of the event chain
    to ensure no tampering or corruption has occurred.
    """
    try:
        logger.info(f"Starting chain integrity verification (positions {from_position}-{to_position})")

        start_time = datetime.utcnow()

        # Verify chain integrity
        integrity_result = await ledger.verify_chain_integrity(
            from_position=from_position,
            to_position=to_position
        )

        end_time = datetime.utcnow()
        verification_time = (end_time - start_time).total_seconds()

        logger.info(f"Chain integrity verification completed in {verification_time:.2f}s: {'✓' if integrity_result.is_valid else '✗'}")

        return ChainIntegrityResponse(
            is_valid=integrity_result.is_valid,
            total_events=integrity_result.total_events,
            verification_time=verification_time,
            chain_breaks=integrity_result.chain_breaks,
            merkle_anchors_verified=integrity_result.merkle_anchors_verified,
            last_verified_position=integrity_result.last_verified_position
        )

    except Exception as e:
        logger.error(f"Chain integrity verification failed: {str(e)}")
        raise HTTPException(status_code=500, detail="Chain verification failed")

@router.post("/bundles", response_model=StoreBundleResponse)
async def store_bundle(
    request: StoreBundleRequest,
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:write"]))
):
    """
    Store a data bundle in the ledger

    Stores large data bundles with cryptographic signatures
    in the distributed storage system linked to the ledger.
    """
    try:
        logger.info(f"Storing bundle {request.bundle_id} for case {request.case_id}")

        # Calculate bundle hash
        import hashlib
        bundle_hash = hashlib.sha256(request.bundle_data).hexdigest()

        # Store bundle
        bundle_record = await ledger.store_bundle(
            bundle_id=request.bundle_id,
            case_id=request.case_id,
            bundle_data=request.bundle_data,
            bundle_hash=bundle_hash,
            signature_ed25519=request.signature_ed25519,
            public_key_id=request.public_key_id
        )

        logger.info(f"Bundle {request.bundle_id} stored successfully ({len(request.bundle_data)} bytes)")

        return StoreBundleResponse(
            bundle_id=bundle_record.bundle_id,
            case_id=bundle_record.case_id,
            stored_at=bundle_record.stored_at,
            bundle_hash=bundle_record.bundle_hash,
            storage_location=bundle_record.storage_location,
            size_bytes=bundle_record.size_bytes
        )

    except ValueError as e:
        logger.warning(f"Invalid bundle storage request: {str(e)}")
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        logger.error(f"Failed to store bundle {request.bundle_id}: {str(e)}")
        raise HTTPException(status_code=500, detail="Internal server error")

@router.get("/bundles/{bundle_id}")
async def get_bundle(
    bundle_id: str,
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:read"]))
):
    """
    Get bundle by bundle ID

    Retrieves a stored data bundle and its metadata.
    Large bundles are streamed to avoid memory issues.
    """
    try:
        bundle_record = await ledger.get_bundle(bundle_id)

        if not bundle_record:
            raise HTTPException(status_code=404, detail=f"Bundle {bundle_id} not found")

        # For small bundles, return inline
        if bundle_record.size_bytes <= 1024 * 1024:  # 1MB
            bundle_data = await ledger.get_bundle_data(bundle_id)

            return {
                "bundle_id": bundle_record.bundle_id,
                "case_id": bundle_record.case_id,
                "stored_at": bundle_record.stored_at,
                "bundle_hash": bundle_record.bundle_hash,
                "size_bytes": bundle_record.size_bytes,
                "signature_ed25519": bundle_record.signature_ed25519,
                "public_key_id": bundle_record.public_key_id,
                "data": bundle_data
            }

        # For large bundles, return metadata and streaming endpoint
        else:
            return {
                "bundle_id": bundle_record.bundle_id,
                "case_id": bundle_record.case_id,
                "stored_at": bundle_record.stored_at,
                "bundle_hash": bundle_record.bundle_hash,
                "size_bytes": bundle_record.size_bytes,
                "signature_ed25519": bundle_record.signature_ed25519,
                "public_key_id": bundle_record.public_key_id,
                "stream_url": f"/ledger/bundles/{bundle_id}/stream"
            }

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Failed to get bundle {bundle_id}: {str(e)}")
        raise HTTPException(status_code=500, detail="Internal server error")

@router.get("/bundles/{bundle_id}/stream")
async def stream_bundle(
    bundle_id: str,
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:read"]))
):
    """
    Stream bundle data for large bundles

    Streams large bundle data to avoid memory issues.
    """
    try:
        bundle_record = await ledger.get_bundle(bundle_id)

        if not bundle_record:
            raise HTTPException(status_code=404, detail=f"Bundle {bundle_id} not found")

        # Stream bundle data
        async def generate_bundle_stream():
            chunk_size = 8192  # 8KB chunks
            bundle_data = await ledger.get_bundle_data(bundle_id)

            for i in range(0, len(bundle_data), chunk_size):
                chunk = bundle_data[i:i + chunk_size]
                yield chunk

        return StreamingResponse(
            generate_bundle_stream(),
            media_type="application/octet-stream",
            headers={
                "Content-Disposition": f"attachment; filename={bundle_id}.bin",
                "X-Bundle-Hash": bundle_record.bundle_hash,
                "X-Bundle-Size": str(bundle_record.size_bytes)
            }
        )

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Failed to stream bundle {bundle_id}: {str(e)}")
        raise HTTPException(status_code=500, detail="Internal server error")

@router.get("/health", response_model=LedgerHealthResponse)
async def health_check(
    ledger: PostgreSQLLedger = Depends(get_ledger)
):
    """
    Ledger health check

    Comprehensive health check of all ledger components
    including database, storage, TSA, and chain integrity.
    """
    try:
        logger.debug("Performing ledger health check")

        # Get health status
        health_status = await ledger.get_health_status()

        return LedgerHealthResponse(
            status=health_status.overall_status,
            database_status=health_status.database_status,
            storage_status=health_status.storage_status,
            tsa_status=health_status.tsa_status,
            chain_status=health_status.chain_status,
            performance_metrics=health_status.performance_metrics,
            timestamp=datetime.utcnow()
        )

    except Exception as e:
        logger.error(f"Health check failed: {str(e)}")
        return LedgerHealthResponse(
            status="unhealthy",
            database_status="error",
            storage_status="error",
            tsa_status="error",
            chain_status="error",
            performance_metrics={},
            timestamp=datetime.utcnow()
        )

@router.get("/metrics", response_model=LedgerMetricsResponse)
async def get_metrics(
    ledger: PostgreSQLLedger = Depends(get_ledger),
    current_user = Depends(get_current_user),
    permissions = Depends(require_permissions(["ledger:read"]))
):
    """
    Get ledger performance metrics

    Returns current performance metrics including throughput,
    latency, and system utilization statistics.
    """
    try:
        logger.debug("Retrieving ledger metrics")

        # Get performance metrics
        metrics = await ledger.get_performance_metrics()

        return LedgerMetricsResponse(
            events_per_second=metrics.events_per_second,
            total_events=metrics.total_events,
            total_cases=metrics.total_cases,
            total_bundles=metrics.total_bundles,
            average_latency_ms=metrics.average_latency_ms,
            chain_length=metrics.chain_length,
            storage_usage_mb=metrics.storage_usage_mb,
            timestamp=datetime.utcnow()
        )

    except Exception as e:
        logger.error(f"Failed to get metrics: {str(e)}")
        raise HTTPException(status_code=500, detail="Metrics unavailable")

# === BACKGROUND TASKS ===

async def _schedule_integrity_check(ledger: PostgreSQLLedger, chain_position: int):
    """Schedule background chain integrity check"""

    # Only check integrity every 1000 events to avoid overhead
    if chain_position % 1000 == 0:
        logger.info(f"Scheduling background integrity check at position {chain_position}")

        try:
            integrity_result = await ledger.verify_chain_integrity()

            if not integrity_result.is_valid:
                logger.error(f"Chain integrity check failed at position {chain_position}: {integrity_result.chain_breaks}")
            else:
                logger.info(f"Chain integrity verified up to position {integrity_result.last_verified_position}")

        except Exception as e:
            logger.error(f"Background integrity check failed: {str(e)}")

# === EXPORTS ===

__all__ = [
    "router",
    "CreateCaseRequest", "CreateCaseResponse",
    "RecordEventRequest", "RecordEventResponse",
    "StoreBundleRequest", "StoreBundleResponse",
    "ChainIntegrityResponse",
    "LedgerHealthResponse", "LedgerMetricsResponse"
]
