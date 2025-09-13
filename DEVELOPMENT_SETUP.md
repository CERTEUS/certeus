# 🚀 CERTEUS Development Setup Guide

> **ONBOARDING GUIDE FOR NEW DEVELOPERS & AGENTS**  
> Step-by-step instructions to get CERTEUS running locally  
> Estimated Setup Time: 15 minutes

## 🎯 Prerequisites

### Required Software
- **Python 3.11+** (recommended: 3.11.9)
- **Docker & Docker Compose** (for infrastructure services)
- **Git** (for repository access)
- **VS Code** (recommended IDE with extensions)

### Recommended VS Code Extensions
- Python
- Pylance  
- Docker
- PostgreSQL
- Git Graph

## ⚡ Quick Start (15 minutes)

### Step 1: Clone Repository
```bash
git clone https://github.com/CERTEUS/control.git
cd control/workspaces/certeus
```

### Step 2: Setup Python Environment
```bash
# Create virtual environment
python -m venv .venv

# Activate environment
# Windows:
.\.venv\Scripts\activate
# Linux/macOS:
source .venv/bin/activate

# Upgrade pip and install dependencies
python -m pip install -U pip wheel setuptools
python -m pip install -r requirements.txt
```

### Step 3: Verify Infrastructure (Already Running!)
```bash
# Check if services are running
docker ps

# You should see these containers:
# - control-postgres
# - control-redis  
# - control-minio
# - control-grafana
# - control-prometheus
```

### Step 4: Run Tests to Verify Setup
```bash
# Quick verification - unit tests only (2 minutes)
python -m pytest tests/ --ignore=tests/integration/ --ignore=tests/performance/ -q

# Expected output: 469 passed, 2 skipped

# Full test suite with infrastructure (5 minutes)  
python -m pytest tests/ --ignore tests/integration/test_a2_ledger_integration.py -q

# Expected output: 530+ tests, mostly passing
```

### Step 5: Start Development Server
```bash
# Start CERTEUS API Gateway
python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000 --reload

# Verify API is running
curl http://127.0.0.1:8000/health
# Expected: {"status": "healthy"}
```

## 🧪 **TESTING QUICK REFERENCE**

### Essential Test Commands
```bash
# Daily development - fast feedback (30 seconds)
pytest tests/ --ignore=tests/integration/ --ignore=tests/performance/ -x

# Feature testing - with infrastructure (2 minutes)
pytest tests/ --ignore tests/integration/test_a2_ledger_integration.py --tb=short

# Coverage report (3 minutes)
pytest tests/ --ignore tests/integration/test_a2_ledger_integration.py --cov=. --cov-report=term-missing

# Specific test debugging
pytest tests/path/to/test.py::test_function -vvv --pdb
```

### Test Categories Available
- ✅ **469 Unit Tests** - No external dependencies
- ✅ **65+ Integration Tests** - Require PostgreSQL, Redis, MinIO
- ✅ **7+ Performance Tests** - Database benchmarks

## 🔧 **INFRASTRUCTURE ACCESS**

All external services are **ALREADY RUNNING** via Docker Compose:

| Service        | Endpoint         | Credentials                  |
| -------------- | ---------------- | ---------------------------- |
| **PostgreSQL** | `localhost:5432` | `control / control_dev_pass` |
| **Redis**      | `localhost:6379` | (no auth)                    |
| **MinIO S3**   | `localhost:9000` | `minioadmin / minioadmin`    |
| **Grafana**    | `localhost:3000` | `admin / admin`              |

See `INFRASTRUCTURE_ACCESS.md` for complete details.

## 📂 **PROJECT STRUCTURE**

```
certeus/
├── 📁 core/              # Core business logic
├── 📁 services/          # Microservices (API Gateway, ProofGate, etc.)
├── 📁 tests/            # Test suite (541 tests total)
│   ├── 📁 api/          # API endpoint tests
│   ├── 📁 integration/  # Integration tests
│   ├── 📁 performance/  # Performance benchmarks
│   └── 📁 services/     # Service layer tests
├── 📁 monitoring/       # Observability (Grafana, Prometheus)
├── 📁 infra/           # Docker infrastructure
├── 📁 docs/            # Documentation (328 files)
└── 📁 migrations/      # Database schemas
```

## 🎯 **DEVELOPMENT WORKFLOW**

### Daily Development Cycle
```bash
# 1. Pull latest changes
git pull origin main

# 2. Run unit tests (quick verification)
pytest tests/ --ignore=tests/integration/ --ignore=tests/performance/ -q

# 3. Start development server
python -m uvicorn services.api_gateway.main:app --reload

# 4. Make changes...

# 5. Run relevant tests
pytest tests/path/to/relevant/tests/ -v

# 6. Run full test suite before commit
pytest tests/ --ignore tests/integration/test_a2_ledger_integration.py --tb=short
```

### Code Quality Checks
```bash
# Format code
ruff format .

# Lint code  
ruff check .

# Type checking
mypy .

# Run all quality checks
ruff format . && ruff check . && mypy .
```

## 🚨 **TROUBLESHOOTING**

### Common Issues & Solutions

**1. Tests Failing Due to Missing Services**
```bash
# Check infrastructure status
docker ps

# Restart services if needed
docker restart control-postgres control-redis control-minio
```

**2. Python Environment Issues**
```bash
# Recreate virtual environment
deactivate
rm -rf .venv
python -m venv .venv
source .venv/bin/activate  # or .\.venv\Scripts\activate on Windows
pip install -r requirements.txt
```

**3. Database Connection Errors**
```bash
# Verify PostgreSQL is accessible
docker exec control-postgres pg_isready -U control

# Check test databases exist
docker exec control-postgres psql -U control -l | grep certeus
```

**4. Port Already in Use (8000)**
```bash
# Find process using port
netstat -an | findstr :8000    # Windows
lsof -i :8000                  # Linux/macOS

# Kill process or use different port
python -m uvicorn services.api_gateway.main:app --port 8001
```

### Getting Help

1. **Documentation**: Check `docs/` folder for specific topics
2. **Infrastructure**: See `INFRASTRUCTURE_ACCESS.md`
3. **Test Issues**: See `TEST_SUITE_STATUS.md`
4. **Code Quality**: Follow patterns in existing codebase

## 🎉 **VERIFICATION CHECKLIST**

After setup, verify everything works:

- [ ] **Python Environment**: `python --version` shows 3.11+
- [ ] **Dependencies**: `pip list | grep fastapi` shows FastAPI installed
- [ ] **Infrastructure**: `docker ps` shows 7+ containers running
- [ ] **Database**: Tests pass with `pytest tests/services/test_ledger_integration.py -v`
- [ ] **API Server**: `curl localhost:8000/health` returns healthy status
- [ ] **Unit Tests**: `pytest tests/ --ignore=tests/integration/ --ignore=tests/performance/ -q` passes
- [ ] **Code Quality**: `ruff check .` shows no errors

## 🚀 **YOU'RE READY!**

With this setup complete, you have:
- ✅ Full CERTEUS development environment
- ✅ 541 tests available (530+ runnable)
- ✅ Complete infrastructure stack
- ✅ Enterprise-grade tooling

**Start coding and testing immediately!** 🎯
