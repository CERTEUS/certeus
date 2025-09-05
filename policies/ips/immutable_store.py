# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | FILE: policy/ips/immutable_store.py                                 |
# | ROLE:                                                               |
# |  PL: Append-only magazyn polityk (IPS), adresowalny hashami.        |
# |  EN: Append-only Immutable Policy Store (IPS), hash-addressable.    |
# +=====================================================================+

"""PL: Minimalny IPS: write_once(key,h), get(h), list(). EN: Minimal IPS."""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path

@dataclass(frozen=True)
class PolicyRecord:
    hash_hex: str
    path: Path
    metadata: dict[str, str]

class ImmutablePolicyStore:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.root.mkdir(parents=True, exist_ok=True)

    def write_once(self, content: bytes, meta: dict[str, str]) -> PolicyRecord:
        h = sha256(content).hexdigest()
        p = self.root / f"{h}.yaml"
        if p.exists():
            return PolicyRecord(h, p, meta)
        p.write_bytes(content)
        (self.root / f"{h}.meta.json").write_text(str(meta), encoding="utf-8")
        return PolicyRecord(h, p, meta)

    def get(self, hash_hex: str) -> bytes:
        return (self.root / f"{hash_hex}.yaml").read_bytes()

    def exists(self, hash_hex: str) -> bool:
        return (self.root / f"{hash_hex}.yaml").exists()
