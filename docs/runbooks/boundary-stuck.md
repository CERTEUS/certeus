# Runbook: Boundary stuck

1. Sprawdź `POST /v1/boundary/reconstruct` (delta_bits).
2. Jeśli `delta_bits > 0`:
   - przejrzyj `bits_delta_map`
   - wymuś synchronizację shardu (job: boundary-resync)
3. Zweryfikuj kotwice czasu i podpisy (cosign, in-toto).
