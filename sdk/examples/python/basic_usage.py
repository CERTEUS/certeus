#!/usr/bin/env python3
"""CERTEUS Python SDK - Basic Usage Example"""

from certeus_sdk import CerteusAPIError, CerteusClient


def basic_usage():
    """Basic SDK usage example."""
    # Initialize client
    client = CerteusClient(
        base_url='https://api.certeus.dev',
        api_key='your-api-key',
        tenant_id='your-tenant-id'
    )
    
    try:
        # Health check
        health_response = client.health()
        print(f"API Status: {health_response.data['status']}")
        
        # Get OpenAPI specification
        spec_response = client.openapi()
        print(f"API Version: {spec_response.data['info']['version']}")
        
    except CerteusAPIError as e:
        print(f"API Error: {e} (Status: {e.status_code})")
    except Exception as e:
        print(f"Unexpected error: {e}")

if __name__ == "__main__":
    basic_usage()
