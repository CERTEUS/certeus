#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: security/frost.py                                    |
# | ROLE: FROST 2-of-3 aggregation/verification (stub)        |
# | PLIK: security/frost.py                                    |
# | ROLA: Agregacja/weryfikacja FROST 2‑z‑3 (stub pod CI)      |
# +-------------------------------------------------------------+

"""
PL: Minimalny stub agregatora FROST dla CI: nie implementuje kryptografii;
    sprawdza quorum (>= threshold) i wylicza deterministyczny "agg" jako
    sha256 z ciągu podpisów/signerów.

EN: Minimal FROST aggregator stub for CI: no cryptography; checks threshold
    and computes deterministic "agg" as sha256 of concatenated inputs.
"""

from __future__ import annotations

from dataclasses import dataclass, asdict
from hashlib import sha256
from typing import Any


@dataclass(frozen=True)
class FrostQuorum:
    scheme: str
    threshold: int
    participants: int
    signers: list[str]
    agg: str  # hex digest (stub)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def aggregate(signers: list[str], threshold: int, participants: int, *, scheme: str = "frost-ed25519") -> FrostQuorum:
    if not isinstance(signers, list) or not all(isinstance(s, str) and s for s in signers):
        raise ValueError("invalid signers")
    if not isinstance(threshold, int) or threshold <= 0:
        raise ValueError("invalid threshold")
    if not isinstance(participants, int) or participants < threshold:
        raise ValueError("invalid participants")
    # Deterministic aggregator over sorted signers
    uniq = sorted({s.strip() for s in signers if s.strip()})
    h = sha256(('|'.join(uniq)).encode('utf-8')).hexdigest()
    return FrostQuorum(scheme=scheme, threshold=threshold, participants=participants, signers=uniq, agg=h)


def verify_quorum(obj: dict[str, Any]) -> bool:
    """
    PL/EN: Verify minimal FROST quorum object structure and threshold >=2, signers>=threshold.
    """
    if not isinstance(obj, dict):
        return False
    try:
        thr = int(obj.get('threshold'))
        parts = int(obj.get('participants')) if obj.get('participants') is not None else thr
        signers = obj.get('signers') or []
        scheme = str(obj.get('scheme') or '')
        agg = str(obj.get('agg') or '')
        if thr < 2:
            return False
        if parts < thr:
            return False
        if not isinstance(signers, list) or len(signers) < thr or not all(isinstance(s, str) and s for s in signers):
            return False
        if 'frost' not in scheme:
            return False
        if not isinstance(agg, str) or len(agg) < 16:
            return False
        # Deterministic consistency of agg
        expect = aggregate(signers, thr, parts, scheme=scheme).agg
        return agg == expect
    except Exception:
        return False


__all__ = ["FrostQuorum", "aggregate", "verify_quorum"]

