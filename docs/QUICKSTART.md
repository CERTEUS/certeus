# Quick Start

Set up CERTEUS for local evaluation or development in minutes.

## Prerequisites

- Python 3.11+ or 3.12
- Node.js 18+ (for TypeScript tooling)
- Docker (optional, for local stack)

## 60‑Second Setup

```bash
git clone https://github.com/CERTEUS/certeus.git
cd certeus
python -m venv .venv
source .venv/bin/activate  # Windows: .venv\\Scripts\\activate
pip install -r requirements.txt
```

## Run the API (local)

```bash
uvicorn certeus.api.main:app --host 0.0.0.0 --port 8000 --reload
```

Verify: `curl http://localhost:8000/health`

## Python SDK

See: [SDK_PY_QUICKSTART.md](SDK_PY_QUICKSTART.md) and [sdk/python.md](sdk/python.md)

