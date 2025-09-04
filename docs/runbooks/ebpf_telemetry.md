#!/usr/bin/env markdown

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: docs/runbooks/ebpf_telemetry.md                       |
# | ROLE: Runbook SRE (eBPF/bpftrace)                           |
# +-------------------------------------------------------------+

## Cel (W1)
- OTel + korelacja + profilowanie dostępne out-of-the-box.
- eBPF: szybki smoke do inspekcji syscalls procesu `uvicorn` (Linux only).

## Wymagania
- Linux z włączonym BPF i `bpftrace` w PATH.
- Uvicorn uruchomiony lokalnie: `PYTHON -m uvicorn services.api_gateway.main:app`.

## Smoke (bpftrace)
- Jednorazowy plik: `scripts/ebpf/uvicorn_syscalls.bt` (5 s okno):
  - Uruchom: `sudo bpftrace scripts/ebpf/uvicorn_syscalls.bt`
  - Wynik: top lista syscalli wykonywanych przez `uvicorn`.

## Smoke (Python wrapper)
- `scripts/sre/ebpf_uvicorn_smoke.py` (no-root, best-effort):
  - Uruchom: `PYTHON scripts/sre/ebpf_uvicorn_smoke.py`
  - Zachowanie: jeśli nie Linux/brak `bpftrace` → SKIP (0).

## Korelacja z OTel
- Włącz OTEL: `OTEL_ENABLED=1` oraz mock OTLP: `scripts/otel/mock_otlp.py`.
- Korelacja w nagłówkach odpowiedzi:
  - `X-Correlation-ID` oraz `X-CERTEUS-PCO-correlation.*`.
  - Przy aktywnym OTel: `X-Trace-Id`.

## Profilowanie (opcjonalne)
- `PROFILE_HTTP=1` zapisuje `.pstats` do `out/profiles/` dla wolnych żądań.
- Próg: `PROFILE_THRESHOLD_MS` (domyślnie 50).

## Notatki operacyjne
- CI nie wymusza eBPF (platform-specific). Skrypt jest informacyjny.
- Dalsze kroki (W2+): BCC/bpftrace p95 per path via kprobes/uprobes lub eBPF exporter.

