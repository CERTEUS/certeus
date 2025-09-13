#!/usr/bin/env python3
"""CERTEUS Python SDK - Context Manager Example"""

from collections.abc import Generator
from contextlib import contextmanager
import time

from certeus_sdk import CerteusAPIError, CerteusClient


@contextmanager
def certeus_client_context(
    base_url: str, api_key: str = None, tenant_id: str = None
) -> Generator[CerteusClient, None, None]:
    """Context manager for CERTEUS client with automatic cleanup."""
    client = CerteusClient(base_url=base_url, api_key=api_key, tenant_id=tenant_id)

    start_time = time.time()
    print(f"Initializing CERTEUS client for: {base_url}")

    try:
        # Verify connection
        health = client.health()
        if health.data.get('status') != 'ok':
            raise ConnectionError("API health check failed")

        yield client

    except CerteusAPIError as e:
        print(f"CERTEUS API Error: {e}")
        raise
    except Exception as e:
        print(f"Unexpected error: {e}")
        raise
    finally:
        duration = time.time() - start_time
        print(f"CERTEUS client session completed in {duration:.2f}s")


def example_with_context():
    """Example using context manager."""
    with certeus_client_context(base_url='http://localhost:8000', api_key='your-api-key', tenant_id='demo') as client:
        # Get API specification
        spec = client.openapi()
        paths = spec.data.get('paths', {})
        print(f"API has {len(paths)} endpoints")

        # List some paths
        for path in list(paths.keys())[:5]:
            print(f"  - {path}")


if __name__ == "__main__":
    example_with_context()
