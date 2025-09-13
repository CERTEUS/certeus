# 🔧 CERTEUS Infrastructure Access Guide

> **CRITICAL INFORMATION FOR ALL DEVELOPERS & AGENTS**  
> Last Updated: 12 września 2025  
> Status: ✅ PRODUCTION READY

## 🚀 Infrastructure Overview

CERTEUS platform runs on **Docker Compose** infrastructure providing all external services required for development and testing. All services are **ALREADY RUNNING** and ready for use.

## 📊 Services Status

| Service        | Status    | Endpoint          | Purpose                         |
| -------------- | --------- | ----------------- | ------------------------------- |
| **PostgreSQL** | ✅ RUNNING | `localhost:5432`  | Main database & test databases  |
| **Redis**      | ✅ RUNNING | `localhost:6379`  | Caching & session storage       |
| **MinIO (S3)** | ✅ RUNNING | `localhost:9000`  | Object storage for ProofBundles |
| **Grafana**    | ✅ RUNNING | `localhost:3000`  | Monitoring dashboards           |
| **Prometheus** | ✅ RUNNING | `localhost:9090`  | Metrics collection              |
| **SonarQube**  | ✅ RUNNING | `localhost:9002`  | Code quality analysis           |
| **Ollama**     | ✅ RUNNING | `localhost:11434` | Local LLM services              |

## 🔑 Access Credentials

### PostgreSQL Database
```bash
# Primary Database
Host: localhost:5432
Database: control
Username: control
Password: control_dev_pass

# Test Databases (for integration tests)
Database: certeus_integration_test
Database: certeus_test
Username: certeus_test
Password: password
```

### Redis
```bash
Host: localhost:6379
Password: (none - no authentication required)
```

### MinIO S3-Compatible Storage
```bash
Endpoint: http://localhost:9000
Console: http://localhost:9001
Access Key: minioadmin
Secret Key: minioadmin
```

### Grafana Monitoring
```bash
URL: http://localhost:3000
Username: admin
Password: admin
```

### Prometheus Metrics
```bash
URL: http://localhost:9090
Authentication: (none required)
```

### SonarQube Code Quality
```bash
URL: http://localhost:9002
Username: admin
Password: admin
```

## 🧪 Test Database Configuration

### Test Databases Available
- **`certeus_integration_test`** - For integration tests requiring full database schema
- **`certeus_test`** - For performance and load testing
- **Schema Applied:** ✅ Ledger schema from `migrations/001_ledger_schema.sql`

### Database Connection Examples

**Python (asyncpg):**
```python
import asyncpg

# For integration tests
conn = await asyncpg.connect(
    "postgresql://certeus_test:password@localhost/certeus_integration_test"
)

# For performance tests  
conn = await asyncpg.connect(
    "postgresql://certeus_test:password@localhost/certeus_test"
)
```

**Environment Variables:**
```bash
export DATABASE_URL="postgresql://certeus_test:password@localhost/certeus_integration_test"
export REDIS_URL="redis://localhost:6379"
export S3_ENDPOINT="http://localhost:9000"
export S3_ACCESS_KEY="minioadmin"
export S3_SECRET_KEY="minioadmin"
```

## ⚡ Quick Access Commands

### Check Infrastructure Status
```bash
# View running containers
docker ps

# Check logs for specific service
docker logs control-postgres
docker logs control-redis
docker logs control-minio

# Access database directly
docker exec -it control-postgres psql -U control -d control
```

### Restart Services (if needed)
```bash
# Restart all services
docker restart control-postgres control-redis control-minio

# Or recreate from docker-compose
docker compose -f /f/projekty/control/docker-compose.testing.yml restart
```

## 🔧 Service Health Checks

All services include health monitoring. Check status:

```bash
# PostgreSQL
docker exec control-postgres pg_isready -U control

# Redis
docker exec control-redis redis-cli ping

# MinIO
curl -I http://localhost:9000/minio/health/live
```

## 📱 Web Interfaces

| Service           | URL                   | Description            |
| ----------------- | --------------------- | ---------------------- |
| **MinIO Console** | http://localhost:9001 | S3 bucket management   |
| **Grafana**       | http://localhost:3000 | Performance dashboards |
| **Prometheus**    | http://localhost:9090 | Raw metrics            |
| **SonarQube**     | http://localhost:9002 | Code quality reports   |

## 🚨 Important Notes

1. **Infrastructure is ALWAYS RUNNING** - No need to start services manually
2. **Test databases are PRE-CONFIGURED** with schema and test user
3. **All ports are exposed** for development and testing
4. **Data persists** across container restarts via Docker volumes
5. **Services auto-restart** on system reboot

## 🔍 Troubleshooting

### Common Issues

**Port Already in Use:**
- Infrastructure is already running (expected behavior)
- Check `docker ps` to confirm services are healthy

**Database Connection Failed:**
- Verify PostgreSQL is running: `docker exec control-postgres pg_isready -U control`
- Check credentials match exactly as listed above

**Test Database Not Found:**
- Databases are pre-created: `certeus_integration_test`, `certeus_test`
- User `certeus_test` has full access to both databases

### Emergency Reset
```bash
# Nuclear option - recreate all infrastructure
docker compose -f /f/projekty/control/docker-compose.testing.yml down -v
docker compose -f /f/projekty/control/docker-compose.testing.yml up -d

# Wait for services to be ready
sleep 30

# Recreate test databases and user
docker exec control-postgres createuser -U control certeus_test
docker exec control-postgres createdb -U control -O certeus_test certeus_integration_test
docker exec control-postgres createdb -U control -O certeus_test certeus_test
```

---

**🎯 READY FOR DEVELOPMENT**  
All services are operational and configured for immediate use by developers and AI agents.
