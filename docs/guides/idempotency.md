#!/usr/bin/env markdown

# Idempotency w Devices API (TTL + metryki)

- Nagłówek żądania: `X-Idempotency-Key` (stabilny identyfikator klienta per operacja).
- Nagłówek odpowiedzi: `X-Idempotent-Replay` — `"1"` jeśli odpowiedź z cache; `"0"` jeśli nowa.
- TTL cache można nadpisać zmienną `IDEMP_TTL_SEC` (sekundy), domyślnie `300`.
- Metryka Prometheus: `certeus_idempotent_replay_total{path,hit}`.

## Przykłady

```bash
# Pierwsze wywołanie → X-Idempotent-Replay: 0
curl -i -sS -X POST \
  "$CER_BASE/v1/devices/horizon_drive/plan" \
  -H 'Content-Type: application/json' \
  -H 'X-Idempotency-Key: idem-123' \
  -d '{"target_horizon":0.25}' | sed -n '1,30p'

# Drugie wywołanie tym samym kluczem → X-Idempotent-Replay: 1
curl -i -sS -X POST \
  "$CER_BASE/v1/devices/horizon_drive/plan" \
  -H 'Content-Type: application/json' \
  -H 'X-Idempotency-Key: idem-123' \
  -d '{"target_horizon":0.25}' | sed -n '1,30p'
```

## TTL=0 (wyłączenie cache)

```bash
export IDEMP_TTL_SEC=0
# X-Idempotent-Replay będzie '0' przy każdym wywołaniu
```

