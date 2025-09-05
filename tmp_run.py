from fastapi.testclient import TestClient
from services.api_gateway.main import app
from services.api_gateway.routers import pfs_dht
c = TestClient(app)
print('BEFORE', pfs_dht._MEM_DB)
print('announce A', c.post('/v1/pfs/dht/announce', json={'node':'node-A','competencies':['lexqft.*','proof.*'],'capacity':2}).status_code)
print('announce B', c.post('/v1/pfs/dht/announce', json={'node':'node-B','competencies':['cfe.geodesic','lexenith.*'],'capacity':1}).status_code)
print('AFTER', pfs_dht._MEM_DB)
print('query lexqft.tunnel', c.get('/v1/pfs/dht/query', params={'competency':'lexqft.tunnel'}).json())
