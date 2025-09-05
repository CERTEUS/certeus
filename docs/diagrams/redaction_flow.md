#!/usr/bin/env markdown

# Redaction Flow (Mermaid)

```mermaid
flowchart LR
  A[Payload JSON] --> B[Load PII patterns]
  B --> C[Scan strings with regex]
  C -->|hits| D{STRICT_REDACTION?}
  D -- yes --> E[Fail (exit 1)]
  D -- no --> F[OK (exit 0)]
  C -->|no hits| F
```
