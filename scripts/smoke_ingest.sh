# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |                 Smoke test for /v1/ingest                   |
# +-------------------------------------------------------------+

set -euo pipefail

printf '%s' 'hello CERTEUS' > sample.txt
printf '%s' '%PDF-1.4 dummy' > sample.pdf

echo "[INFO] Health"
curl -sS http://127.0.0.1:8000/health

echo "[INFO] Ingest TXT"
curl -sS -i -F "file=@sample.txt;type=text/plain" http://127.0.0.1:8000/v1/ingest | grep "HTTP/1.1 200"

echo "[INFO] Ingest PDF"
curl -sS -i -F "file=@sample.pdf;type=application/pdf" http://127.0.0.1:8000/v1/ingest | grep "HTTP/1.1 200"

echo "[INFO] Done"
