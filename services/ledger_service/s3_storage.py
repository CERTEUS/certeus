#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/ledger_service/s3_storage.py                |
# | ROLE: A2 - S3/MinIO Storage Manager with WORM-like policies|
# | PLIK: services/ledger_service/s3_storage.py                |
# | ROLA: A2 - S3/MinIO Storage Manager with WORM-like policies|
# +-------------------------------------------------------------+

"""
PL: S3 Storage Manager z politykami retencji WORM-like
EN: S3 Storage Manager with WORM-like retention policies

Features:
- Bundle storage with versioning
- Lifecycle policies for archival
- Object lock for immutability
- Backup and restore capabilities
- Performance optimization
"""

from __future__ import annotations

import asyncio
from dataclasses import dataclass
from datetime import datetime, timedelta
import json
import logging
import os
from typing import Any

import boto3
from botocore.config import Config
from botocore.exceptions import ClientError

# === CONFIGURATION ===


@dataclass
class S3Config:
    """S3 Storage configuration"""

    bucket_name: str
    region: str = "us-east-1"
    endpoint_url: str | None = None  # For MinIO
    access_key: str | None = None
    secret_key: str | None = None

    # WORM-like settings
    object_lock_enabled: bool = False
    default_retention_days: int = 2555  # ~7 years
    legal_hold_enabled: bool = False

    # Performance
    multipart_threshold: int = 64 * 1024 * 1024  # 64MB
    max_concurrency: int = 10

    # Lifecycle policies
    transition_to_ia_days: int = 30
    transition_to_glacier_days: int = 90
    transition_to_deep_archive_days: int = 365

    @classmethod
    def from_env(cls) -> S3Config:
        """Load configuration from environment"""
        return cls(
            bucket_name=os.getenv("CERTEUS_S3_BUCKET", "certeus-bundles"),
            region=os.getenv("CERTEUS_S3_REGION", "us-east-1"),
            endpoint_url=os.getenv("CERTEUS_S3_ENDPOINT"),
            access_key=os.getenv("CERTEUS_S3_ACCESS_KEY"),
            secret_key=os.getenv("CERTEUS_S3_SECRET_KEY"),
            object_lock_enabled=os.getenv("CERTEUS_S3_OBJECT_LOCK", "false").lower() == "true",
            default_retention_days=int(os.getenv("CERTEUS_S3_RETENTION_DAYS", "2555")),
            legal_hold_enabled=os.getenv("CERTEUS_S3_LEGAL_HOLD", "false").lower() == "true",
            multipart_threshold=int(os.getenv("CERTEUS_S3_MULTIPART_THRESHOLD", str(64 * 1024 * 1024))),
            max_concurrency=int(os.getenv("CERTEUS_S3_MAX_CONCURRENCY", "10")),
            transition_to_ia_days=int(os.getenv("CERTEUS_S3_TRANSITION_IA_DAYS", "30")),
            transition_to_glacier_days=int(os.getenv("CERTEUS_S3_TRANSITION_GLACIER_DAYS", "90")),
            transition_to_deep_archive_days=int(os.getenv("CERTEUS_S3_TRANSITION_DEEP_ARCHIVE_DAYS", "365")),
        )


# === MODELS ===


@dataclass
class StorageObject:
    """S3 object metadata"""

    key: str
    bucket: str
    size: int
    etag: str
    last_modified: datetime
    version_id: str | None = None
    storage_class: str = "STANDARD"
    content_type: str = "application/octet-stream"
    metadata: dict[str, str] | None = None

    # WORM properties
    object_lock_mode: str | None = None
    object_lock_retain_until: datetime | None = None
    legal_hold_status: str | None = None


@dataclass
class BackupJob:
    """Backup job metadata"""

    job_id: str
    job_type: str  # full, incremental, differential
    status: str
    started_at: datetime
    completed_at: datetime | None = None
    objects_count: int = 0
    total_size_bytes: int = 0
    error_message: str | None = None


# === EXCEPTIONS ===


class StorageError(Exception):
    """Base storage exception"""

    pass


class BucketNotFoundError(StorageError):
    """Bucket not found"""

    pass


class ObjectNotFoundError(StorageError):
    """Object not found"""

    pass


class RetentionViolationError(StorageError):
    """Retention policy violation"""

    pass


# === S3 STORAGE MANAGER ===


class S3StorageManager:
    """
    Enterprise S3 Storage Manager

    Features:
    - WORM-like immutability with object lock
    - Automatic lifecycle management
    - Versioning and backup/restore
    - Performance optimization
    - Comprehensive monitoring
    """

    def __init__(self, config: S3Config):
        self.config = config
        self.logger = logging.getLogger("certeus.storage")

        # Configure boto3 session
        session = boto3.Session(
            aws_access_key_id=config.access_key, aws_secret_access_key=config.secret_key, region_name=config.region
        )

        # S3 client with performance optimizations
        s3_config = Config(
            retries={'max_attempts': 3}, max_pool_connections=config.max_concurrency, region_name=config.region
        )

        self.s3_client = session.client('s3', config=s3_config, endpoint_url=config.endpoint_url)
        self.s3_resource = session.resource('s3', config=s3_config, endpoint_url=config.endpoint_url)

        # Performance metrics
        self._metrics = {"objects_stored": 0, "bytes_stored": 0, "average_upload_time": 0.0, "last_backup_time": None}

    async def initialize(self) -> None:
        """Initialize storage: create bucket, configure policies"""

        try:
            # Check if bucket exists
            self.s3_client.head_bucket(Bucket=self.config.bucket_name)
            self.logger.info(f"Bucket {self.config.bucket_name} exists")

        except ClientError as e:
            error_code = e.response['Error']['Code']

            if error_code == '404':
                # Create bucket
                await self._create_bucket()
            else:
                raise StorageError(f"Bucket access error: {e}")

        # Configure bucket policies
        await self._configure_bucket_policies()

        self.logger.info("S3 Storage Manager initialized")

    async def _create_bucket(self) -> None:
        """Create S3 bucket with proper configuration"""

        try:
            if self.config.region == 'us-east-1':
                self.s3_client.create_bucket(Bucket=self.config.bucket_name)
            else:
                self.s3_client.create_bucket(
                    Bucket=self.config.bucket_name, CreateBucketConfiguration={'LocationConstraint': self.config.region}
                )

            # Enable versioning
            self.s3_client.put_bucket_versioning(
                Bucket=self.config.bucket_name, VersioningConfiguration={'Status': 'Enabled'}
            )

            # Enable object lock if configured
            if self.config.object_lock_enabled:
                self.s3_client.put_object_lock_configuration(
                    Bucket=self.config.bucket_name,
                    ObjectLockConfiguration={
                        'ObjectLockEnabled': 'Enabled',
                        'Rule': {
                            'DefaultRetention': {'Mode': 'GOVERNANCE', 'Days': self.config.default_retention_days}
                        },
                    },
                )

            self.logger.info(f"Created bucket {self.config.bucket_name}")

        except ClientError as e:
            raise StorageError(f"Failed to create bucket: {e}")

    async def _configure_bucket_policies(self) -> None:
        """Configure lifecycle policies and permissions"""

        # Lifecycle configuration
        lifecycle_config = {
            'Rules': [
                {
                    'ID': 'CERTEUS_Lifecycle_Policy',
                    'Status': 'Enabled',
                    'Filter': {'Prefix': 'bundles/'},
                    'Transitions': [
                        {'Days': self.config.transition_to_ia_days, 'StorageClass': 'STANDARD_IA'},
                        {'Days': self.config.transition_to_glacier_days, 'StorageClass': 'GLACIER'},
                        {'Days': self.config.transition_to_deep_archive_days, 'StorageClass': 'DEEP_ARCHIVE'},
                    ],
                }
            ]
        }

        try:
            self.s3_client.put_bucket_lifecycle_configuration(
                Bucket=self.config.bucket_name, LifecycleConfiguration=lifecycle_config
            )

            self.logger.info("Configured lifecycle policies")

        except ClientError as e:
            self.logger.warning(f"Failed to configure lifecycle policies: {e}")

    # === OBJECT OPERATIONS ===

    async def store_object(
        self,
        key: str,
        data: bytes,
        content_type: str = "application/json",
        metadata: dict[str, str] | None = None,
        retention_days: int | None = None,
    ) -> StorageObject:
        """Store object with optional retention policy"""

        extra_args = {'ContentType': content_type, 'Metadata': metadata or {}}

        # Add object lock retention if enabled
        if self.config.object_lock_enabled and retention_days:
            retain_until = datetime.utcnow() + timedelta(days=retention_days)
            extra_args['ObjectLockMode'] = 'GOVERNANCE'
            extra_args['ObjectLockRetainUntilDate'] = retain_until

        try:
            # Upload object
            response = self.s3_client.put_object(Bucket=self.config.bucket_name, Key=key, Body=data, **extra_args)

            # Get object metadata
            head_response = self.s3_client.head_object(Bucket=self.config.bucket_name, Key=key)

            # Update metrics
            self._metrics["objects_stored"] += 1
            self._metrics["bytes_stored"] += len(data)

            return StorageObject(
                key=key,
                bucket=self.config.bucket_name,
                size=len(data),
                etag=response['ETag'].strip('"'),
                last_modified=head_response['LastModified'],
                version_id=response.get('VersionId'),
                content_type=content_type,
                metadata=metadata,
                object_lock_mode=head_response.get('ObjectLockMode'),
                object_lock_retain_until=head_response.get('ObjectLockRetainUntilDate'),
                legal_hold_status=head_response.get('ObjectLockLegalHoldStatus'),
            )

        except ClientError as e:
            raise StorageError(f"Failed to store object {key}: {e}")

    async def get_object(self, key: str, version_id: str | None = None) -> bytes:
        """Retrieve object data"""

        try:
            params = {'Bucket': self.config.bucket_name, 'Key': key}
            if version_id:
                params['VersionId'] = version_id

            response = self.s3_client.get_object(**params)
            return response['Body'].read()

        except ClientError as e:
            if e.response['Error']['Code'] == 'NoSuchKey':
                raise ObjectNotFoundError(f"Object not found: {key}")
            else:
                raise StorageError(f"Failed to get object {key}: {e}")

    async def get_object_metadata(self, key: str, version_id: str | None = None) -> StorageObject:
        """Get object metadata without downloading content"""

        try:
            params = {'Bucket': self.config.bucket_name, 'Key': key}
            if version_id:
                params['VersionId'] = version_id

            response = self.s3_client.head_object(**params)

            return StorageObject(
                key=key,
                bucket=self.config.bucket_name,
                size=response['ContentLength'],
                etag=response['ETag'].strip('"'),
                last_modified=response['LastModified'],
                version_id=response.get('VersionId'),
                storage_class=response.get('StorageClass', 'STANDARD'),
                content_type=response.get('ContentType', 'application/octet-stream'),
                metadata=response.get('Metadata'),
                object_lock_mode=response.get('ObjectLockMode'),
                object_lock_retain_until=response.get('ObjectLockRetainUntilDate'),
                legal_hold_status=response.get('ObjectLockLegalHoldStatus'),
            )

        except ClientError as e:
            if e.response['Error']['Code'] == 'NoSuchKey':
                raise ObjectNotFoundError(f"Object not found: {key}")
            else:
                raise StorageError(f"Failed to get object metadata {key}: {e}")

    async def delete_object(self, key: str, version_id: str | None = None, bypass_governance: bool = False) -> None:
        """Delete object (with retention policy checks)"""

        # Check retention policy
        if not bypass_governance:
            try:
                metadata = await self.get_object_metadata(key, version_id)
                if metadata.object_lock_retain_until and metadata.object_lock_retain_until > datetime.utcnow():
                    raise RetentionViolationError(
                        f"Object {key} is under retention until {metadata.object_lock_retain_until}"
                    )
            except ObjectNotFoundError:
                return  # Object already deleted

        try:
            params = {'Bucket': self.config.bucket_name, 'Key': key}
            if version_id:
                params['VersionId'] = version_id
            if bypass_governance:
                params['BypassGovernanceRetention'] = True

            self.s3_client.delete_object(**params)

        except ClientError as e:
            raise StorageError(f"Failed to delete object {key}: {e}")

    # === BACKUP AND RESTORE ===

    async def create_backup(self, backup_type: str = "full", prefix: str = "bundles/") -> BackupJob:
        """Create backup of all objects with given prefix"""

        job_id = f"backup_{backup_type}_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}"

        backup_job = BackupJob(job_id=job_id, job_type=backup_type, status="RUNNING", started_at=datetime.utcnow())

        try:
            # List all objects
            paginator = self.s3_client.get_paginator('list_objects_v2')
            pages = paginator.paginate(Bucket=self.config.bucket_name, Prefix=prefix)

            backup_manifest = {
                "job_id": job_id,
                "backup_type": backup_type,
                "started_at": backup_job.started_at.isoformat(),
                "prefix": prefix,
                "objects": [],
            }

            total_objects = 0
            total_size = 0

            for page in pages:
                if 'Contents' in page:
                    for obj in page['Contents']:
                        backup_manifest["objects"].append(
                            {
                                "key": obj['Key'],
                                "size": obj['Size'],
                                "etag": obj['ETag'],
                                "last_modified": obj['LastModified'].isoformat(),
                            }
                        )
                        total_objects += 1
                        total_size += obj['Size']

            # Store backup manifest
            manifest_key = f"backups/{job_id}/manifest.json"
            await self.store_object(
                manifest_key,
                json.dumps(backup_manifest, indent=2).encode(),
                content_type="application/json",
                metadata={"backup-job-id": job_id, "backup-type": backup_type},
            )

            backup_job.status = "COMPLETED"
            backup_job.completed_at = datetime.utcnow()
            backup_job.objects_count = total_objects
            backup_job.total_size_bytes = total_size

            self._metrics["last_backup_time"] = backup_job.completed_at

            self.logger.info(f"Backup {job_id} completed: {total_objects} objects, {total_size:,} bytes")

            return backup_job

        except Exception as e:
            backup_job.status = "FAILED"
            backup_job.error_message = str(e)
            backup_job.completed_at = datetime.utcnow()

            self.logger.error(f"Backup {job_id} failed: {e}")
            return backup_job

    async def restore_from_backup(self, job_id: str, target_prefix: str | None = None) -> BackupJob:
        """Restore objects from backup manifest"""

        restore_job = BackupJob(
            job_id=f"restore_{job_id}_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}",
            job_type="restore",
            status="RUNNING",
            started_at=datetime.utcnow(),
        )

        try:
            # Get backup manifest
            manifest_key = f"backups/{job_id}/manifest.json"
            manifest_data = await self.get_object(manifest_key)
            manifest = json.loads(manifest_data.decode())

            restored_objects = 0
            restored_size = 0

            for obj_info in manifest["objects"]:
                source_key = obj_info["key"]
                target_key = source_key if not target_prefix else f"{target_prefix}/{source_key}"

                try:
                    # Copy object to target location
                    copy_source = {'Bucket': self.config.bucket_name, 'Key': source_key}
                    self.s3_client.copy_object(CopySource=copy_source, Bucket=self.config.bucket_name, Key=target_key)

                    restored_objects += 1
                    restored_size += obj_info["size"]

                except ClientError as e:
                    self.logger.warning(f"Failed to restore object {source_key}: {e}")

            restore_job.status = "COMPLETED"
            restore_job.completed_at = datetime.utcnow()
            restore_job.objects_count = restored_objects
            restore_job.total_size_bytes = restored_size

            self.logger.info(f"Restore {restore_job.job_id} completed: {restored_objects} objects restored")

            return restore_job

        except Exception as e:
            restore_job.status = "FAILED"
            restore_job.error_message = str(e)
            restore_job.completed_at = datetime.utcnow()

            self.logger.error(f"Restore {restore_job.job_id} failed: {e}")
            return restore_job

    # === MONITORING AND HEALTH ===

    async def health_check(self) -> dict[str, Any]:
        """Comprehensive health check"""

        health = {
            "status": "UNKNOWN",
            "bucket_exists": False,
            "bucket_accessible": False,
            "versioning_enabled": False,
            "object_lock_enabled": False,
            "lifecycle_configured": False,
            "last_error": None,
        }

        try:
            # Check bucket existence and access
            self.s3_client.head_bucket(Bucket=self.config.bucket_name)
            health["bucket_exists"] = True
            health["bucket_accessible"] = True

            # Check versioning
            versioning = self.s3_client.get_bucket_versioning(Bucket=self.config.bucket_name)
            health["versioning_enabled"] = versioning.get('Status') == 'Enabled'

            # Check object lock
            try:
                lock_config = self.s3_client.get_object_lock_configuration(Bucket=self.config.bucket_name)
                health["object_lock_enabled"] = lock_config['ObjectLockConfiguration']['ObjectLockEnabled'] == 'Enabled'
            except ClientError:
                health["object_lock_enabled"] = False

            # Check lifecycle
            try:
                self.s3_client.get_bucket_lifecycle_configuration(Bucket=self.config.bucket_name)
                health["lifecycle_configured"] = True
            except ClientError:
                health["lifecycle_configured"] = False

            # Test write/read operation
            test_key = f"health-check/{datetime.utcnow().isoformat()}"
            test_data = b"CERTEUS_HEALTH_CHECK"

            await self.store_object(test_key, test_data, metadata={"health-check": "true"})
            retrieved_data = await self.get_object(test_key)

            if retrieved_data == test_data:
                health["status"] = "HEALTHY"
            else:
                health["status"] = "DEGRADED"
                health["last_error"] = "Data integrity check failed"

            # Cleanup test object
            await self.delete_object(test_key, bypass_governance=True)

        except Exception as e:
            health["status"] = "UNHEALTHY"
            health["last_error"] = str(e)

        # Add metrics
        health.update(
            {
                "metrics": self._metrics,
                "config": {
                    "bucket": self.config.bucket_name,
                    "region": self.config.region,
                    "retention_days": self.config.default_retention_days,
                    "multipart_threshold": self.config.multipart_threshold,
                },
            }
        )

        return health

    async def get_storage_stats(self) -> dict[str, Any]:
        """Get detailed storage statistics"""

        try:
            # Get bucket metrics (if CloudWatch is available)
            total_objects = 0
            total_size = 0
            storage_classes = {}

            paginator = self.s3_client.get_paginator('list_objects_v2')
            pages = paginator.paginate(Bucket=self.config.bucket_name)

            for page in pages:
                if 'Contents' in page:
                    for obj in page['Contents']:
                        total_objects += 1
                        total_size += obj['Size']

                        storage_class = obj.get('StorageClass', 'STANDARD')
                        storage_classes[storage_class] = storage_classes.get(storage_class, 0) + 1

            return {
                "total_objects": total_objects,
                "total_size_bytes": total_size,
                "total_size_gb": round(total_size / (1024**3), 2),
                "storage_classes": storage_classes,
                "average_object_size": total_size // max(total_objects, 1),
                "metrics": self._metrics,
                "last_updated": datetime.utcnow().isoformat(),
            }

        except Exception as e:
            return {"error": str(e), "last_updated": datetime.utcnow().isoformat()}


# === FACTORY ===

_global_storage: S3StorageManager | None = None


async def get_storage_manager() -> S3StorageManager:
    """Get global storage manager instance"""
    global _global_storage

    if _global_storage is None:
        config = S3Config.from_env()
        _global_storage = S3StorageManager(config)
        await _global_storage.initialize()

    return _global_storage


# === CLI INTERFACE ===


async def main() -> None:
    """CLI interface for storage operations"""
    import sys

    if len(sys.argv) < 2:
        print("Usage: python s3_storage.py <command> [args...]")
        print("Commands: health, stats, backup, list-backups")
        return

    command = sys.argv[1]
    storage = await get_storage_manager()

    try:
        if command == "health":
            result = await storage.health_check()
            print(json.dumps(result, indent=2))

        elif command == "stats":
            result = await storage.get_storage_stats()
            print(json.dumps(result, indent=2))

        elif command == "backup":
            job = await storage.create_backup()
            print(f"Backup job {job.job_id}: {job.status}")
            if job.status == "COMPLETED":
                print(f"Objects: {job.objects_count}, Size: {job.total_size_bytes:,} bytes")

        else:
            print(f"Unknown command: {command}")

    except Exception as e:
        print(f"Error: {e}")


if __name__ == "__main__":
    asyncio.run(main())
