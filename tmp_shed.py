from fastapi.testclient import TestClient
from services.api_gateway.main import app
c = TestClient(app)
r=c.post('/v1/qtm/measure', json={'operator':'L','source':'shed-test'})
print('STATUS', r.status_code)
