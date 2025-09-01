#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ledger_service/cosmic_merkle.py            |

# | ROLE: Project module.                                       |

# | PLIK: services/ledger_service/cosmic_merkle.py            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Minimalna, deterministyczna implementacja Merkle z blokadą RLock. Brak PII —

    operujemy na heksowych hashach. Interfejs zgodny z testami.

EN: Minimal deterministic Merkle with RLock. No PII — operates on hex hashes.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===


# --- blok --- Importy ----------------------------------------------------------

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from threading import RLock

# --- blok --- Pomocnicze funkcje hashujące ------------------------------------


def _h(x: str, y: str) -> str:
    """Hash two hex nodes (order-independent canonicalization)."""

    a = bytes.fromhex(x)

    b = bytes.fromhex(y)

    left, right = (a, b) if a <= b else (b, a)

    return sha256(left + right).hexdigest()


def _hh(x: bytes) -> str:
    """Hash raw bytes to hex."""

    return sha256(x).hexdigest()


# --- blok --- Struktury danych -------------------------------------------------


@dataclass(frozen=True)
class MerklePathElem:
    """One step in a Merkle proof path."""

    sibling: str  # hex digest of sibling node

    position: str  # "L" or "R" (informative; verification uses canonical order)


@dataclass(frozen=True)
class MerkleReceipt:
    """Proof that a leaf is included under a Merkle root."""

    root: str

    path: list[MerklePathElem]

    leaf: str  # leaf = H(rid_hash || bundle_hash) as hex


# --- blok --- Rdzeń drzewa Merkle ----------------------------------------------


class CosmicMerkle:
    """

    In-memory append-only Merkle ledger.

    For production, back with durable storage or periodic snapshots.

    """

    def __init__(self) -> None:
        self._lock = RLock()

        self._leaves: list[str] = []  # hex digests

        self._tree: list[list[str]] = []  # levels: 0=leaves, last=root

    @staticmethod
    def _leaf_of(rid_hash: str, bundle_hash: str) -> str:
        payload = bytes.fromhex(rid_hash) + bytes.fromhex(bundle_hash)

        return _hh(payload)

    def _rebuild(self) -> None:
        # Build full tree from leaves

        levels: list[list[str]] = []

        cur = list(self._leaves)

        levels.append(cur)

        while len(cur) > 1:
            nxt: list[str] = []

            it = iter(cur)

            for a in it:
                try:
                    b = next(it)

                    nxt.append(_h(a, b))

                except StopIteration:
                    # odd leaf promoted up (hash with itself)

                    nxt.append(_h(a, a))

            levels.append(nxt)

            cur = nxt

        self._tree = levels

    def _root(self) -> str:
        if not self._tree:
            return _hh(b"")  # deterministic empty root

        return self._tree[-1][0]

    def anchor_bundle(self, rid_hash: str, bundle_hash: str) -> MerkleReceipt:
        """

        Append bundle leaf and return receipt.

        - rid_hash, bundle_hash are hex digests (lowercase)

        """

        leaf = self._leaf_of(rid_hash, bundle_hash)

        with self._lock:
            self._leaves.append(leaf)

            self._rebuild()

            path = self._build_path(len(self._leaves) - 1)

            return MerkleReceipt(root=self._root(), path=path, leaf=leaf)

    def _build_path(self, index: int) -> list[MerklePathElem]:
        path: list[MerklePathElem] = []

        if not self._tree or index >= len(self._tree[0]):
            return path

        idx = index

        for level in self._tree[:-1]:
            # find sibling index

            if idx % 2 == 0:  # left
                sib_idx = idx + 1 if idx + 1 < len(level) else idx

                position = "L"

            else:
                sib_idx = idx - 1

                position = "R"

            sibling = level[sib_idx]

            path.append(MerklePathElem(sibling=sibling, position=position))

            # parent index

            idx //= 2

        return path

    def get_bundle_proof(self, rid_hash: str, bundle_hash: str) -> MerkleReceipt | None:
        leaf = self._leaf_of(rid_hash, bundle_hash)

        with self._lock:
            try:
                idx = self._leaves.index(leaf)

            except ValueError:
                return None

            path = self._build_path(idx)

            return MerkleReceipt(root=self._root(), path=path, leaf=leaf)

    @staticmethod
    def verify_proof(receipt: MerkleReceipt) -> bool:
        """Verify receipt.path from leaf to root."""

        cur = receipt.leaf

        for elem in receipt.path:
            cur = _h(cur, elem.sibling)

        return cur == receipt.root


# --- blok --- Facade (poziom modułu) -------------------------------------------


_LEDGER = CosmicMerkle()


def anchor_bundle(rid_hash: str, bundle_hash: str) -> MerkleReceipt:
    return _LEDGER.anchor_bundle(rid_hash, bundle_hash)


def get_bundle_proof(rid_hash: str, bundle_hash: str) -> MerkleReceipt | None:
    return _LEDGER.get_bundle_proof(rid_hash, bundle_hash)


def verify_proof(receipt: MerkleReceipt) -> bool:
    return CosmicMerkle.verify_proof(receipt)
