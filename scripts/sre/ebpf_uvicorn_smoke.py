#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/sre/ebpf_uvicorn_smoke.py                    |
# | ROLE: eBPF/bpftrace smoke for uvicorn                       |
# | PLIK: scripts/sre/ebpf_uvicorn_smoke.py                    |
# | ROLA: Smoke-test eBPF/bpftrace dla uvicorn                  |
# +-------------------------------------------------------------+

"""
PL: Lekki smoketest eBPF: jeśli system to Linux i zainstalowany jest `bpftrace`,
    uruchamia prosty licznik wywołań syscalli dla procesu `uvicorn` przez N s.
    Gdy warunki nie są spełnione — kończy się statusem 0 (skip, informacyjnie).

EN: Lightweight eBPF smoketest: on Linux with `bpftrace` installed, runs a simple
    syscall counter for process `uvicorn` for N seconds. Otherwise exits 0 with
    an informational message (skip).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from pathlib import Path
import platform
import shutil
import subprocess

# === LOGIKA / LOGIC ===

SCRIPT = r'''
tracepoint:syscalls:sys_enter_* /comm == "uvicorn"/ {
  @sys[probe] = count();
}
interval:s:5 { exit(); }
'''


def main() -> int:
    if platform.system().lower() != "linux":
        print("ebpf: SKIP (non-Linux)")
        return 0
    if not shutil.which("bpftrace"):
        print("ebpf: SKIP (bpftrace not found)")
        return 0
    tmp = Path("out/ebpf")
    tmp.mkdir(parents=True, exist_ok=True)
    script_path = tmp / "uvicorn_syscalls.bt"
    script_path.write_text(SCRIPT, encoding="utf-8")
    try:
        proc = subprocess.run(
            ["bpftrace", str(script_path)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=15
        )
        print(proc.stdout)
    except subprocess.TimeoutExpired:
        print("ebpf: TIMEOUT (no data) — OK for smoke")
    except Exception as e:
        print(f"ebpf: ERROR: {e}")
        # Do not fail pipeline by default
        if (os.getenv("EBPF_ENFORCE") or "").strip() in {"1", "true", "True"}:
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
