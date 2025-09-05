#!/usr/bin/env python3
"""
PL: Smoke dla PFS DHT: announce→query→publish_path, zapisuje do out/.
EN: PFS DHT smoke: announce→query→publish_path, writes to out/.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import requests as rq


def main() -> int:
    base = os.getenv("CER_BASE", "http://127.0.0.1:8000").rstrip("/")
    out = Path("out")
    out.mkdir(parents=True, exist_ok=True)

    def get(url: str):
        r = rq.get(base + url, timeout=3)
        r.raise_for_status()
        return r.json()

    def post(url: str, body: dict):
        r = rq.post(base + url, json=body, timeout=3)
        r.raise_for_status()
        return r.json()

    a1 = post(
        "/v1/pfs/dht/announce",
        {"node": "Node-A", "competencies": ["lexqft.*", "proof.*"], "capacity": 2, "ttl_sec": 3600},
    )
    a2 = post(
        "/v1/pfs/dht/announce",
        {"node": "Node-B", "competencies": ["cfe.geodesic", "lexenith.*"], "capacity": 1, "ttl_sec": 3600},
    )
    q1 = get("/v1/pfs/dht/query?competency=lexqft.tunnel")
    pub = post(
        "/v1/pfs/dht/publish_path", {"case": "DHT-SMOKE", "path": ["lexqft.tunnel", "cfe.geodesic", "proof.publish"]}
    )

    (out / "dht_announce_a.json").write_text(json.dumps(a1, indent=2), encoding="utf-8")
    (out / "dht_announce_b.json").write_text(json.dumps(a2, indent=2), encoding="utf-8")
    (out / "dht_query_lexqft.json").write_text(json.dumps(q1, indent=2), encoding="utf-8")
    (out / "dht_publish.json").write_text(json.dumps(pub, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
