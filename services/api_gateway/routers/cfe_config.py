#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/cfe_config.py           |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/cfe_config.py           |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Konfiguracja CFE (stubs): mapy lensingu per domena oraz progi
    heurystyk lock dla horyzontu. Obsługa zewnętrznego pliku JSON
    (ENV `CERTEUS_CFE_LENSING_CONFIG` lub `data/cfe_lensing.json`).

EN: CFE configuration (stubs): domain-specific lensing maps and
    lock heuristics thresholds for horizon. Supports external JSON
    (ENV `CERTEUS_CFE_LENSING_CONFIG` or `data/cfe_lensing.json`).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path
import threading
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===

_DEFAULT_LENSING_WEIGHTS: dict[str, dict[str, float]] = {
    "LEX": {"precedent:K_2001": 0.42, "precedent:III_2020": 0.28},
    "FIN": {"reg:MiFID2:best_execution": 0.31, "esma:guidelines": 0.24},
    "MED": {"icd10:I21": 0.37, "icd10:E11": 0.22, "loinc:718-7": 0.18},
    "SEC": {"nist:SP800-53:AC-2": 0.33, "iso27001:A.12": 0.26, "cwe:79": 0.19},
    "CODE": {"cwe:79": 0.35, "owasp:top10:a03": 0.27, "rfc:9110": 0.14},
}

_DEFAULT_DOMAINS_LOCK = {"MED", "SEC", "CODE", "FIN"}
_DEFAULT_SEVERITY_LOCK = {"high", "critical"}

_ROOT = Path(__file__).resolve().parents[2]
_DEFAULT_CONFIG_FILE = _ROOT / "data" / "cfe_lensing.json"
_CONFIG_ENV = "CERTEUS_CFE_LENSING_CONFIG"

# Runtime cache + watcher state
_CFG_LOCK = threading.Lock()
_CFG_WEIGHTS: dict[str, dict[str, float]] = {
    k: dict(v) for k, v in _DEFAULT_LENSING_WEIGHTS.items()
}
_CFG_DOMAINS: set[str] = set(_DEFAULT_DOMAINS_LOCK)
_CFG_SEVERITIES: set[str] = set(_DEFAULT_SEVERITY_LOCK)
_CFG_PATH: Path | None = None
_CFG_MTIME: float = 0.0
_WATCHER_STARTED = False


def _config_path() -> Path | None:
    p = os.getenv(_CONFIG_ENV)
    if p:
        return Path(p)
    if _DEFAULT_CONFIG_FILE.exists():
        return _DEFAULT_CONFIG_FILE
    return None


def _clamp01(x: Any) -> float:
    try:
        v = float(x)
    except Exception:
        v = 0.0
    return float(max(0.0, min(1.0, v)))


def _parse_config(
    data: dict[str, Any],
) -> tuple[dict[str, dict[str, float]], set[str], set[str]]:
    w_cfg: dict[str, dict[str, float]] = {}
    try:
        w_raw = data.get("lensing", {})  # type: ignore[assignment]
        for dom, mapping in dict(w_raw).items():  # type: ignore[assignment]
            dom_u = str(dom).strip().upper() or "LEX"
            out: dict[str, float] = {}
            for k, val in dict(mapping).items():
                out[str(k)] = _clamp01(val)
            if out:
                w_cfg[dom_u] = out
    except Exception:
        w_cfg = {}
    try:
        lock = data.get("lock", {})  # type: ignore[assignment]
        d_set = {
            str(x).strip().upper() for x in lock.get("domains", []) if str(x).strip()
        }
        s_set = {
            str(x).strip().lower() for x in lock.get("severities", []) if str(x).strip()
        }
    except Exception:
        d_set = set()
        s_set = set()
    return w_cfg, d_set, s_set


def _refresh_config_if_changed() -> None:
    global _CFG_PATH, _CFG_MTIME, _CFG_WEIGHTS, _CFG_DOMAINS, _CFG_SEVERITIES
    path = _config_path()
    try:
        mtime = path.stat().st_mtime if path and path.exists() else 0.0
    except Exception:
        mtime = 0.0
    with _CFG_LOCK:
        if path is None or not path.exists():
            _CFG_PATH = None
            _CFG_MTIME = 0.0
            _CFG_WEIGHTS = {k: dict(v) for k, v in _DEFAULT_LENSING_WEIGHTS.items()}
            _CFG_DOMAINS = set(_DEFAULT_DOMAINS_LOCK)
            _CFG_SEVERITIES = set(_DEFAULT_SEVERITY_LOCK)
            return
        if _CFG_PATH == path and _CFG_MTIME == mtime:
            return
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return
        w_cfg, d_set, s_set = _parse_config(data)
        base = {k: dict(v) for k, v in _DEFAULT_LENSING_WEIGHTS.items()}
        for dom, mapping in w_cfg.items():
            base.setdefault(dom, {})
            base[dom].update(mapping)
        _CFG_WEIGHTS = base
        _CFG_DOMAINS = set(d_set) if d_set else set(_DEFAULT_DOMAINS_LOCK)
        _CFG_SEVERITIES = set(s_set) if s_set else set(_DEFAULT_SEVERITY_LOCK)
        _CFG_PATH = path
        _CFG_MTIME = mtime


def _load_external_config() -> (
    tuple[dict[str, dict[str, float]], set[str] | None, set[str] | None]
):
    """Return merged external weights and (domains,severities) override sets.

    Reads from cached state; refreshes if file mtime changed.
    """
    _refresh_config_if_changed()
    with _CFG_LOCK:
        return dict(_CFG_WEIGHTS), set(_CFG_DOMAINS), set(_CFG_SEVERITIES)


def current_lensing_weights() -> dict[str, dict[str, float]]:
    ext, _, _ = _load_external_config()
    base = {k: dict(v) for k, v in _DEFAULT_LENSING_WEIGHTS.items()}
    if ext:
        for dom, mapping in ext.items():
            base.setdefault(dom, {})
            base[dom].update(mapping)
    return base


def current_lock_sets() -> tuple[set[str], set[str]]:
    _, d_ext, s_ext = _load_external_config()
    d = set(_DEFAULT_DOMAINS_LOCK)
    s = set(_DEFAULT_SEVERITY_LOCK)
    if d_ext is not None:
        d = set(d_ext)
    if s_ext is not None:
        s = set(s_ext)
    return d, s


def get_lensing_map(domain: str | None) -> tuple[dict[str, float], list[str], str]:
    """Zwraca (mapa_wag, krytyczne_klucze, domena_norm).

    - domain: wejściowa nazwa domeny (None → LEX)
    - krytyczne_klucze: heurystycznie — najwyższy wagowo element
    """

    d = (domain or "LEX").strip().upper()
    weights_all = current_lensing_weights()
    weights = weights_all.get(d) or weights_all.get("LEX", {})
    # Clamp i kopia
    clamped = {k: _clamp01(v) for k, v in weights.items()}
    # Krytyczny: max po wadze (deterministycznie)
    if clamped:
        max_key = max(clamped.items(), key=lambda kv: (kv[1], kv[0]))[0]
        crit = [max_key]
    else:
        crit = []
    return clamped, crit, d


# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
