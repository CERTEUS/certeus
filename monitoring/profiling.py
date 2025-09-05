#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: monitoring/profiling.py                               |
# | ROLE: Optional per-request cProfile                         |
# | PLIK: monitoring/profiling.py                               |
# | ROLA: Opcjonalny cProfile per-zapytanie                      |
# +-------------------------------------------------------------+

"""
PL: Lekki middleware profilujący żądania przy włączonej zmiennej środowiskowej
    `PROFILE_HTTP=1`. Zapisuje artefakty `.pstats` dla najwolniejszych żądań
    (czas > progu) do katalogu `out/profiles/`.

EN: Lightweight per-request profiling middleware enabled by `PROFILE_HTTP=1`.
    Saves `.pstats` artifacts for slow requests (time > threshold) to
    `out/profiles/`.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import cProfile
import os
from pathlib import Path
import time
import typing as _t

from fastapi import FastAPI, Request, Response


def attach_profiling_middleware(app: FastAPI) -> None:
    if (os.getenv("PROFILE_HTTP") or "").strip() not in {"1", "true", "True"}:
        return

    out_dir = Path(os.getenv("PROFILE_OUT", "out/profiles"))
    out_dir.mkdir(parents=True, exist_ok=True)
    threshold_ms = float(os.getenv("PROFILE_THRESHOLD_MS", "50"))

    @app.middleware("http")
    async def _prof_mw(  # type: ignore[override]
        request: Request, call_next: _t.Callable[[Request], Response]
    ) -> Response:
        # Only profile API paths (skip statics)
        path = request.url.path
        if path.startswith("/static") or path.startswith("/app"):
            return await call_next(request)

        prof = cProfile.Profile()
        t0 = time.perf_counter()
        response: Response
        try:
            prof.enable()
            response = await call_next(request)
        finally:
            prof.disable()
        dur_ms = (time.perf_counter() - t0) * 1000.0
        if dur_ms >= threshold_ms:
            # filename with method_path_timestamp
            safe = path.strip("/").replace("/", "_") or "root"
            fname = f"{request.method}_{safe}_{int(time.time())}.pstats"
            prof.dump_stats(str(out_dir / fname))
            try:
                response.headers.setdefault("X-Profile-Saved", fname)
                response.headers.setdefault("X-Profile-Duration-Ms", f"{dur_ms:.2f}")
            except Exception:
                pass
        return response


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
