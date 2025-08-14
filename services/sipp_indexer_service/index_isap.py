from datetime import datetime
import hashlib
import json
import os


def snapshot_pl(act_id: str, out_dir: str):
    os.makedirs(out_dir, exist_ok=True)
    text = f"USTAWA_MOCK::{act_id}::v1"
    sha = hashlib.sha256(text.encode()).hexdigest()
    meta = {
        "act_id": act_id,
        "version": "v1",
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "sha256": sha,
        "source_url": "isap://mock",
    }
    with open(os.path.join(out_dir, f"{act_id}.json"), "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=2)
    return meta
