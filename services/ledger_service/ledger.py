import hashlib, time

def _h(b: bytes): return hashlib.sha256(b).hexdigest()

def record_input(path: str):
    with open(path, "rb") as f:
        data = f.read()
    return {"sha256": _h(data), "timestamp": time.time(), "parent": None}

def record_transform(parent_hash: str, payload: bytes):
    return {"sha256": _h(payload), "timestamp": time.time(), "parent": parent_hash}

def record_export(parent_hash: str, payload: bytes):
    return {"sha256": _h(payload), "timestamp": time.time(), "parent": parent_hash}
