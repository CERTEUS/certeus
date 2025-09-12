#!/usr/bin/env python3
"""CERTEUS Python SDK - Advanced Usage Example"""

import asyncio
import logging
import os
from typing import Any, Dict, Optional

from certeus_sdk import CerteusClient, CerteusAPIError

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class CerteusService:
    """Advanced CERTEUS service wrapper with error handling and retries."""
    
    def __init__(self, config: Dict[str, Any]):
        self.client = CerteusClient(
            base_url=config.get('base_url', 'http://localhost:8000'),
            api_key=config.get('api_key'),
            tenant_id=config.get('tenant_id'),
            timeout_seconds=config.get('timeout', 30),
            retry_count=config.get('retry_count', 3),
            retry_delay_seconds=config.get('retry_delay', 1.0)
        )
        self.logger = logger
    
    def health_check(self) -> bool:
        """Check API health status."""
        try:
            response = self.client.health()
            is_healthy = response.data.get('status') == 'ok'
            self.logger.info(f"Health check: {'PASS' if is_healthy else 'FAIL'}")
            return is_healthy
        except CerteusAPIError as e:
            self.logger.error(f"Health check failed: {e}")
            return False
    
    def with_retry(self, operation, *args, **kwargs):
        """Execute operation with retry logic."""
        max_retries = 3
        last_error = None
        
        for attempt in range(max_retries + 1):
            try:
                return operation(*args, **kwargs)
            except Exception as e:
                last_error = e
                if attempt < max_retries:
                    delay = 2 ** attempt
                    self.logger.warning(f"Attempt {attempt + 1} failed, retrying in {delay}s: {e}")
                    time.sleep(delay)
                else:
                    self.logger.error(f"All retry attempts failed: {e}")
        
        raise last_error
    
    def get_api_info(self) -> Optional[Dict[str, Any]]:
        """Get API information with retry."""
        try:
            response = self.with_retry(self.client.openapi)
            return response.data.get('info', {})
        except Exception as e:
            self.logger.error(f"Failed to get API info: {e}")
            return None

def main():
    """Advanced usage example."""
    # Load configuration from environment
    config = {
        'base_url': os.getenv('CERTEUS_API_URL', 'http://localhost:8000'),
        'api_key': os.getenv('CERTEUS_API_KEY'),
        'tenant_id': os.getenv('CERTEUS_TENANT_ID'),
        'timeout': int(os.getenv('CERTEUS_TIMEOUT', '30')),
        'retry_count': int(os.getenv('CERTEUS_RETRY_COUNT', '3'))
    }
    
    # Initialize service
    service = CerteusService(config)
    
    # Health check with retry
    if service.health_check():
        logger.info("Service is healthy")
        
        # Get API information
        api_info = service.get_api_info()
        if api_info:
            logger.info(f"API Version: {api_info.get('version')}")
            logger.info(f"API Title: {api_info.get('title')}")
    else:
        logger.error("Service health check failed")

if __name__ == "__main__":
    main()
