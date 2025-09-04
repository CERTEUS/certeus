#!/usr/bin/env markdown

# PFS / DHT — cURL smoki

## Inspect ProofFS (read-only)

- List cases: `curl -s http://127.0.0.1:8000/v1/pfs/inspect`
- Case paths: `curl -s http://127.0.0.1:8000/v1/pfs/case/CASE-ID`

## DHT Kompetencji

- Announce:
```
curl -s -X POST http://127.0.0.1:8000/v1/pfs/dht/announce \
  -H 'Content-Type: application/json' \
  -d '{"node":"Node-A","competencies":["lexqft.*","proof.*"],"capacity":2}'
```
- Query:
```
curl -s 'http://127.0.0.1:8000/v1/pfs/dht/query?competency=lexqft.tunnel'
```
- Publish path:
```
curl -s -X POST http://127.0.0.1:8000/v1/pfs/dht/publish_path \
  -H 'Content-Type: application/json' \
  -d '{"case":"DHT-CASE","path":["lexqft.tunnel","cfe.geodesic","proof.publish"]}'
```
