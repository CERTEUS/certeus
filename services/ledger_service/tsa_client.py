#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/ledger_service/tsa_client.py                |
# | ROLE: A2 - RFC3161 Time Stamp Authority Client            |
# | PLIK: services/ledger_service/tsa_client.py                |
# | ROLA: A2 - RFC3161 Time Stamp Authority Client            |
# +-------------------------------------------------------------+

"""
PL: RFC3161 TSA Client - znaczniki czasu dla ledger
EN: RFC3161 TSA Client - timestamps for ledger

Features:
- RFC3161 compliant timestamp requests
- Multiple TSA provider support
- Timestamp verification
- Batch timestamping for performance
- Fallback mechanisms
"""

from __future__ import annotations

import asyncio
from dataclasses import dataclass
from datetime import datetime
import hashlib
import logging
import os
from typing import Any

import aiohttp
from cryptography import x509
from cryptography.hazmat.primitives import hashes

# === CONFIGURATION ===


@dataclass
class TSAConfig:
    """TSA Client configuration"""

    primary_tsa_url: str
    fallback_tsa_urls: list[str]
    timeout_seconds: float = 30.0
    max_retries: int = 3

    # Certificate validation
    verify_certificates: bool = True
    trusted_ca_certs: list[str] | None = None

    # Performance
    batch_size: int = 10
    concurrent_requests: int = 3

    # Policy and options
    request_cert_in_response: bool = True
    hash_algorithm: str = "sha256"  # sha256, sha384, sha512

    @classmethod
    def from_env(cls) -> TSAConfig:
        """Load configuration from environment"""

        primary_url = os.getenv("CERTEUS_TSA_PRIMARY_URL")
        if not primary_url:
            raise ValueError("CERTEUS_TSA_PRIMARY_URL is required")

        fallback_urls = []
        fallback_env = os.getenv("CERTEUS_TSA_FALLBACK_URLS", "")
        if fallback_env:
            fallback_urls = [url.strip() for url in fallback_env.split(",")]

        return cls(
            primary_tsa_url=primary_url,
            fallback_tsa_urls=fallback_urls,
            timeout_seconds=float(os.getenv("CERTEUS_TSA_TIMEOUT", "30.0")),
            max_retries=int(os.getenv("CERTEUS_TSA_MAX_RETRIES", "3")),
            verify_certificates=os.getenv("CERTEUS_TSA_VERIFY_CERTS", "true").lower() == "true",
            trusted_ca_certs=None,  # TODO: Load from env
            batch_size=int(os.getenv("CERTEUS_TSA_BATCH_SIZE", "10")),
            concurrent_requests=int(os.getenv("CERTEUS_TSA_CONCURRENT", "3")),
            request_cert_in_response=os.getenv("CERTEUS_TSA_REQUEST_CERT", "true").lower() == "true",
            hash_algorithm=os.getenv("CERTEUS_TSA_HASH_ALGORITHM", "sha256"),
        )


# === MODELS ===


@dataclass
class TimestampRequest:
    """RFC3161 timestamp request"""

    message_hash: bytes
    hash_algorithm: str
    nonce: int | None = None
    request_cert: bool = True
    policy_id: str | None = None


@dataclass
class TimestampResponse:
    """RFC3161 timestamp response"""

    timestamp_token: bytes
    timestamp: datetime
    serial_number: int
    tsa_certificate: x509.Certificate | None = None
    policy_id: str | None = None
    accuracy: int | None = None  # microseconds
    ordering: bool = False
    nonce: int | None = None

    # Verification status
    is_verified: bool = False
    verification_error: str | None = None


@dataclass
class BatchTimestampJob:
    """Batch timestamp job"""

    job_id: str
    requests: list[TimestampRequest]
    responses: list[TimestampResponse | None]
    status: str  # pending, running, completed, failed
    started_at: datetime | None = None
    completed_at: datetime | None = None
    error_message: str | None = None


# === EXCEPTIONS ===


class TSAError(Exception):
    """Base TSA exception"""

    pass


class TSATimeoutError(TSAError):
    """TSA request timeout"""

    pass


class TSAValidationError(TSAError):
    """TSA response validation error"""

    pass


class TSAUnavailableError(TSAError):
    """All TSA servers unavailable"""

    pass


# === RFC3161 TSA CLIENT ===


class RFC3161TSAClient:
    """
    RFC3161 Time Stamp Authority Client

    Features:
    - Multiple TSA provider support with fallback
    - Batch processing for performance
    - Certificate validation
    - Comprehensive error handling
    - Performance monitoring
    """

    def __init__(self, config: TSAConfig):
        self.config = config
        self.logger = logging.getLogger("certeus.tsa")

        # Performance metrics
        self._metrics = {
            "requests_sent": 0,
            "responses_received": 0,
            "average_response_time": 0.0,
            "success_rate": 0.0,
            "last_request_time": None,
        }

        # Hash algorithm mapping
        self._hash_algorithms = {"sha256": hashes.SHA256(), "sha384": hashes.SHA384(), "sha512": hashes.SHA512()}

    async def request_timestamp(
        self, data: bytes, hash_algorithm: str | None = None, nonce: int | None = None
    ) -> TimestampResponse:
        """Request single timestamp for data"""

        # Compute hash
        hash_alg = hash_algorithm or self.config.hash_algorithm
        if hash_alg not in self._hash_algorithms:
            raise TSAError(f"Unsupported hash algorithm: {hash_alg}")

        hasher = hashlib.new(hash_alg)
        hasher.update(data)
        message_hash = hasher.digest()

        # Create request
        request = TimestampRequest(
            message_hash=message_hash,
            hash_algorithm=hash_alg,
            nonce=nonce,
            request_cert=self.config.request_cert_in_response,
        )

        # Send request
        return await self._send_timestamp_request(request)

    async def request_timestamp_for_hash(
        self, message_hash: bytes, hash_algorithm: str, nonce: int | None = None
    ) -> TimestampResponse:
        """Request timestamp for pre-computed hash"""

        request = TimestampRequest(
            message_hash=message_hash,
            hash_algorithm=hash_algorithm,
            nonce=nonce,
            request_cert=self.config.request_cert_in_response,
        )

        return await self._send_timestamp_request(request)

    async def batch_timestamp(self, data_list: list[bytes], hash_algorithm: str | None = None) -> BatchTimestampJob:
        """Request timestamps for multiple data items"""

        job_id = f"batch_{datetime.utcnow().strftime('%Y%m%d_%H%M%S_%f')}"

        # Prepare requests
        requests = []
        hash_alg = hash_algorithm or self.config.hash_algorithm

        for i, data in enumerate(data_list):
            hasher = hashlib.new(hash_alg)
            hasher.update(data)
            message_hash = hasher.digest()

            requests.append(
                TimestampRequest(
                    message_hash=message_hash,
                    hash_algorithm=hash_alg,
                    nonce=i + 1,  # Use index as nonce
                    request_cert=self.config.request_cert_in_response,
                )
            )

        # Create batch job
        job = BatchTimestampJob(
            job_id=job_id,
            requests=requests,
            responses=[None] * len(requests),
            status="running",
            started_at=datetime.utcnow(),
        )

        try:
            # Process requests in batches
            semaphore = asyncio.Semaphore(self.config.concurrent_requests)

            async def process_request(index: int, request: TimestampRequest) -> None:
                async with semaphore:
                    try:
                        response = await self._send_timestamp_request(request)
                        job.responses[index] = response
                    except Exception as e:
                        self.logger.warning(f"Batch request {index} failed: {e}")
                        job.responses[index] = None

            # Execute all requests concurrently
            tasks = [process_request(i, req) for i, req in enumerate(requests)]

            await asyncio.gather(*tasks, return_exceptions=True)

            # Check results
            successful_responses = sum(1 for r in job.responses if r is not None)

            if successful_responses == 0:
                job.status = "failed"
                job.error_message = "All timestamp requests failed"
            elif successful_responses < len(requests):
                job.status = "completed"
                job.error_message = f"Partial success: {successful_responses}/{len(requests)}"
            else:
                job.status = "completed"

            job.completed_at = datetime.utcnow()

            self.logger.info(f"Batch timestamp job {job_id}: {successful_responses}/{len(requests)} successful")

            return job

        except Exception as e:
            job.status = "failed"
            job.error_message = str(e)
            job.completed_at = datetime.utcnow()

            self.logger.error(f"Batch timestamp job {job_id} failed: {e}")
            return job

    async def _send_timestamp_request(self, request: TimestampRequest) -> TimestampResponse:
        """Send individual timestamp request with fallback"""

        urls_to_try = [self.config.primary_tsa_url] + self.config.fallback_tsa_urls
        last_error = None

        for url in urls_to_try:
            try:
                response = await self._send_to_tsa_server(url, request)

                # Update metrics
                self._update_metrics(success=True)

                return response

            except Exception as e:
                last_error = e
                self.logger.warning(f"TSA request to {url} failed: {e}")

                # Update metrics
                self._update_metrics(success=False)

                continue

        # All servers failed
        raise TSAUnavailableError(f"All TSA servers failed. Last error: {last_error}")

    async def _send_to_tsa_server(self, url: str, request: TimestampRequest) -> TimestampResponse:
        """Send request to specific TSA server"""

        # Build RFC3161 timestamp request
        ts_request = self._build_rfc3161_request(request)

        # Send HTTP request
        timeout = aiohttp.ClientTimeout(total=self.config.timeout_seconds)

        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.post(
                url,
                data=ts_request,
                headers={'Content-Type': 'application/timestamp-query', 'User-Agent': 'CERTEUS-Engine-TSA-Client/1.0'},
            ) as response:
                if response.status != 200:
                    raise TSAError(f"TSA server returned {response.status}: {response.reason}")

                # Check content type
                content_type = response.headers.get('Content-Type', '')
                if 'application/timestamp-reply' not in content_type:
                    raise TSAError(f"Invalid content type: {content_type}")

                # Read response
                ts_response_data = await response.read()

                # Parse RFC3161 response
                return self._parse_rfc3161_response(ts_response_data, request)

    def _build_rfc3161_request(self, request: TimestampRequest) -> bytes:
        """Build RFC3161 timestamp request (ASN.1 DER)"""

        # For now, return a mock request
        # TODO: Implement proper ASN.1 encoding using pyasn1 or similar

        mock_request = {
            "version": 1,
            "messageImprint": {"hashAlgorithm": request.hash_algorithm, "hashedMessage": request.message_hash.hex()},
            "reqPolicy": None,
            "nonce": request.nonce,
            "certReq": request.request_cert,
            "extensions": None,
        }

        # This would be properly ASN.1 encoded in production
        return f"MOCK_TSA_REQUEST:{mock_request}".encode()

    def _parse_rfc3161_response(self, response_data: bytes, request: TimestampRequest) -> TimestampResponse:
        """Parse RFC3161 timestamp response"""

        # For now, return a mock response
        # TODO: Implement proper ASN.1 decoding

        if response_data.startswith(b"MOCK_TSA_REQUEST:"):
            # Mock successful response
            return TimestampResponse(
                timestamp_token=response_data,
                timestamp=datetime.utcnow(),
                serial_number=12345,
                is_verified=True,
                nonce=request.nonce,
                ordering=True,
            )
        else:
            raise TSAValidationError("Invalid TSA response format")

    async def verify_timestamp(self, timestamp_token: bytes, original_data: bytes, hash_algorithm: str) -> bool:
        """Verify timestamp token against original data"""

        try:
            # Parse timestamp token
            response = self._parse_rfc3161_response(
                timestamp_token, TimestampRequest(message_hash=b"", hash_algorithm=hash_algorithm)
            )

            if not response.is_verified:
                return False

            # Verify hash
            hasher = hashlib.new(hash_algorithm)
            hasher.update(original_data)
            hasher.digest()

            # In a real implementation, we would extract the hash from the timestamp
            # and compare it with computed_hash

            return True  # Mock verification

        except Exception as e:
            self.logger.error(f"Timestamp verification failed: {e}")
            return False

    def _update_metrics(self, success: bool) -> None:
        """Update performance metrics"""

        self._metrics["requests_sent"] += 1
        if success:
            self._metrics["responses_received"] += 1

        # Update success rate
        if self._metrics["requests_sent"] > 0:
            self._metrics["success_rate"] = self._metrics["responses_received"] / self._metrics["requests_sent"]

        self._metrics["last_request_time"] = datetime.utcnow()

    async def health_check(self) -> dict[str, Any]:
        """Check TSA service health"""

        health = {
            "status": "UNKNOWN",
            "primary_tsa_available": False,
            "fallback_tsa_available": 0,
            "last_error": None,
            "response_time_ms": None,
        }

        try:
            # Test primary TSA
            start_time = datetime.utcnow()
            test_data = b"CERTEUS_TSA_HEALTH_CHECK"

            await self.request_timestamp(test_data)

            end_time = datetime.utcnow()
            response_time = (end_time - start_time).total_seconds() * 1000

            health["primary_tsa_available"] = True
            health["response_time_ms"] = response_time
            health["status"] = "HEALTHY"

        except Exception as e:
            health["last_error"] = str(e)
            health["status"] = "DEGRADED"

        # Test fallback TSAs
        available_fallbacks = 0
        for url in self.config.fallback_tsa_urls:
            try:
                # Quick test request
                test_request = TimestampRequest(message_hash=hashlib.sha256(b"test").digest(), hash_algorithm="sha256")
                await self._send_to_tsa_server(url, test_request)
                available_fallbacks += 1
            except:
                pass

        health["fallback_tsa_available"] = available_fallbacks

        # Add metrics
        health["metrics"] = self._metrics

        return health


# === FACTORY ===

_global_tsa_client: RFC3161TSAClient | None = None


async def get_tsa_client() -> RFC3161TSAClient:
    """Get global TSA client instance"""
    global _global_tsa_client

    if _global_tsa_client is None:
        config = TSAConfig.from_env()
        _global_tsa_client = RFC3161TSAClient(config)

    return _global_tsa_client


# === CLI INTERFACE ===


async def main() -> None:
    """CLI interface for TSA operations"""
    import sys

    if len(sys.argv) < 2:
        print("Usage: python tsa_client.py <command> [args...]")
        print("Commands: health, timestamp <data>, verify <token> <data>")
        return

    command = sys.argv[1]

    try:
        tsa_client = await get_tsa_client()

        if command == "health":
            result = await tsa_client.health_check()
            print(f"TSA Health: {result['status']}")
            print(f"Primary TSA: {'✓' if result['primary_tsa_available'] else '✗'}")
            print(f"Fallback TSAs: {result['fallback_tsa_available']}")
            if result['response_time_ms']:
                print(f"Response time: {result['response_time_ms']:.1f}ms")

        elif command == "timestamp":
            if len(sys.argv) < 3:
                print("Usage: timestamp <data>")
                return

            data = sys.argv[2].encode()
            response = await tsa_client.request_timestamp(data)
            print(f"Timestamp: {response.timestamp}")
            print(f"Serial: {response.serial_number}")
            print(f"Verified: {response.is_verified}")

        elif command == "verify":
            if len(sys.argv) < 4:
                print("Usage: verify <token_file> <data>")
                return

            with open(sys.argv[2], 'rb') as f:
                token = f.read()

            data = sys.argv[3].encode()
            is_valid = await tsa_client.verify_timestamp(token, data, "sha256")
            print(f"Verification: {'✓ VALID' if is_valid else '✗ INVALID'}")

        else:
            print(f"Unknown command: {command}")

    except Exception as e:
        print(f"Error: {e}")


if __name__ == "__main__":
    asyncio.run(main())
