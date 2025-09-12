#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/logging.py                                      |
# | ROLE: Centralized logging configuration                    |
# | PLIK: core/logging.py                                      |
# | ROLA: Scentralizowana konfiguracja logowania               |
# +-------------------------------------------------------------+

"""
PL: System logowania CERTEUS z wsparciem dla formatowania JSON i kolorów
EN: CERTEUS logging system with JSON formatting and color support

Provides centralized logging configuration for all CERTEUS components
with structured JSON output and optional color formatting for development.
"""

from datetime import datetime
import json
import logging
import logging.config
import os
import sys


class CERTEUSFormatter(logging.Formatter):
    """Enhanced formatter for CERTEUS with JSON structure"""

    def __init__(self, use_json: bool = True, use_colors: bool = False):
        super().__init__()
        self.use_json = use_json
        self.use_colors = use_colors

        if use_colors:
            self.colors = {
                'DEBUG': '\033[36m',  # Cyan
                'INFO': '\033[32m',  # Green
                'WARNING': '\033[33m',  # Yellow
                'ERROR': '\033[31m',  # Red
                'CRITICAL': '\033[35m',  # Magenta
                'RESET': '\033[0m',  # Reset
            }
        else:
            self.colors = {}

    def format(self, record: logging.LogRecord) -> str:
        """Format log record"""

        if self.use_json:
            log_entry = {
                'timestamp': datetime.utcnow().isoformat() + 'Z',
                'level': record.levelname,
                'logger': record.name,
                'message': record.getMessage(),
                'module': record.module,
                'function': record.funcName,
                'line': record.lineno,
            }

            # Add exception info if present
            if record.exc_info:
                log_entry['exception'] = self.formatException(record.exc_info)

            # Add extra fields
            for key, value in record.__dict__.items():
                if key not in [
                    'name',
                    'msg',
                    'args',
                    'levelname',
                    'levelno',
                    'pathname',
                    'filename',
                    'module',
                    'lineno',
                    'funcName',
                    'created',
                    'msecs',
                    'relativeCreated',
                    'thread',
                    'threadName',
                    'processName',
                    'process',
                    'message',
                    'exc_info',
                    'exc_text',
                    'stack_info',
                ]:
                    log_entry[key] = value

            return json.dumps(log_entry, ensure_ascii=False)

        else:
            # Simple text format with optional colors
            formatted = f"{datetime.utcnow().isoformat()}Z [{record.levelname:8}] {record.name}: {record.getMessage()}"

            if self.use_colors and record.levelname in self.colors:
                color = self.colors[record.levelname]
                reset = self.colors['RESET']
                formatted = f"{color}{formatted}{reset}"

            return formatted


def setup_logging(
    level: str = "INFO", use_json: bool = None, use_colors: bool = None, log_file: str | None = None
) -> None:
    """
    Setup centralized logging configuration

    Args:
        level: Log level (DEBUG, INFO, WARNING, ERROR, CRITICAL)
        use_json: Use JSON formatting (default: True in production, False in dev)
        use_colors: Use color output (default: True in dev, False in production)
        log_file: Optional file to write logs to
    """

    # Auto-detect environment if not specified
    if use_json is None:
        use_json = os.getenv("CERTEUS_ENV", "development") == "production"

    if use_colors is None:
        use_colors = os.getenv("CERTEUS_ENV", "development") == "development" and sys.stdout.isatty()

    # Create formatter
    formatter = CERTEUSFormatter(use_json=use_json, use_colors=use_colors)

    # Setup console handler
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setFormatter(formatter)

    handlers = [console_handler]

    # Setup file handler if specified
    if log_file:
        file_handler = logging.FileHandler(log_file, encoding='utf-8')
        file_formatter = CERTEUSFormatter(use_json=True, use_colors=False)
        file_handler.setFormatter(file_formatter)
        handlers.append(file_handler)

    # Configure root logger
    logging.basicConfig(level=getattr(logging, level.upper()), handlers=handlers, force=True)

    # Set specific loggers to appropriate levels
    logging.getLogger("asyncio").setLevel(logging.WARNING)
    logging.getLogger("urllib3").setLevel(logging.WARNING)
    logging.getLogger("boto3").setLevel(logging.WARNING)
    logging.getLogger("botocore").setLevel(logging.WARNING)


def get_logger(name: str) -> logging.Logger:
    """
    Get a configured logger for the specified name

    Args:
        name: Logger name (usually module or component name)

    Returns:
        Configured logger instance
    """
    return logging.getLogger(name)


# Initialize default logging if not already configured
if not logging.getLogger().handlers:
    setup_logging()


# Export public interface
__all__ = ['setup_logging', 'get_logger', 'CERTEUSFormatter']
