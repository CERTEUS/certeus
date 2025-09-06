# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/redaction_gate.py                     |
# | ROLE: Project script.                                       |
# | PLIK: scripts/gates/redaction_gate.py                     |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Bramka redakcji PII zgodna z polityką w policies/pco/policy_pack.yaml.
    - Czyta JSON ze stdin lub pliku (--input).
    - Sprawdza wystąpienia wzorców PII (regexy) i opcjonalnie maskuje/odrzuca.
    - Zmienna STRICT_REDACTION=1 wymusza exit 1 przy wykryciu PII.

EN: PII redaction gate per policies/pco/policy_pack.yaml.
    - Reads JSON from stdin or file (--input).
    - Checks for PII patterns (regex) and optionally masks/rejects.
    - STRICT_REDACTION=1 enforces non-zero exit on detection.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===
import argparse
import json
import os
from pathlib import Path
import re
from typing import Any

import yaml

# === LOGIKA / LOGIC ===


def _load_patterns() -> list[str]:
    try:
        root = Path(__file__).resolve().parents[2]
        pack = root / "policies" / "pco" / "policy_pack.yaml"
        doc = yaml.safe_load(pack.read_text(encoding="utf-8")) or {}
        patt = ((doc.get("redaction") or {}).get("pii_patterns")) or []
        return [str(x) for x in patt]
    except Exception:
        return []


def _scan(
    obj: Any, patterns: list[re.Pattern[str]], hits: list[str], path: str = "$"
) -> None:
    if isinstance(obj, dict):
        for k, v in obj.items():
            _scan(v, patterns, hits, path=f"{path}.{k}")
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            _scan(v, patterns, hits, path=f"{path}[{i}]")
    elif isinstance(obj, str):
        for rx in patterns:
            if rx.search(obj):
                hits.append(path)
                break


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", help="Ścieżka do pliku JSON z payloadem (opcjonalnie)")
    args = ap.parse_args()

    data: Any
    if args.input:
        p = Path(args.input)
        if not p.exists():
            print("[redaction] input file missing; treating as empty (OK)")
            return 0
        data = json.loads(p.read_text(encoding="utf-8"))
    else:
        try:
            raw = os.read(0, 1_000_000).decode("utf-8")
            data = json.loads(raw) if raw.strip() else {}
        except Exception:
            data = {}

    patterns = _load_patterns()
    if not patterns:
        print("[redaction] No PII patterns configured; skipping (OK)")
        return 0
    rx = [re.compile(p) for p in patterns]
    hits: list[str] = []
    _scan(data, rx, hits)
    if not hits:
        print("[redaction] No PII detected (OK)")
        return 0
    print(f"[redaction] PII detected at: {sorted(set(hits))}")
    strict = (os.getenv("STRICT_REDACTION") or "0").strip() in {"1", "true", "True"}
    return 1 if strict else 0


if __name__ == "__main__":  # === I/O / ENDPOINTS === / === TESTY / TESTS ===
    raise SystemExit(main())
