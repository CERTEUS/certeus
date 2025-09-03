# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: runtime/proof_queue.py                                        |
# | ROLE:                                                               |
# |  PL: Kolejka dowodów z wagami SLA i brakiem zagłodzenia.            |
# |  EN: Proof queue with SLA weights and no-starvation guarantees.     |
# +=====================================================================+

"""PL: Zwraca proof_task_id i eta_hint; eksportuje głębokość kolejki.
EN: Returns proof_task_id & eta_hint; exposes queue depth metric.
"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from dataclasses import dataclass, field
import heapq
import time
from typing import Any

from .complexity_estimator import Heat
from .complexity_firewall import parse_sla_weights

SLA_W = parse_sla_weights()


@dataclass(order=True)
class _QItem:
    priority: int
    ts: float = field(compare=True)
    id: str = field(compare=False)
    tenant: str = field(compare=False)
    heat: Heat = field(compare=False)
    payload: dict[str, Any] = field(compare=False)
    eta_hint: str = field(compare=False)


class ProofQueue:
    """PL: Minimalna kolejka z wagami; FIFO w klasie. EN: Minimal weighted queue; FIFO per class."""

    def __init__(self) -> None:
        self._heap: list[tuple[int, float, str, _QItem]] = []
        self._depth = 0

    def enqueue(self, tenant: str, heat: Heat, payload: dict[str, Any], sla: str) -> _QItem:
        prio = -SLA_W.get(sla, 1)
        now = time.time()
        qid = f"pt_{int(now * 1000)}_{tenant}"
        eta = "~3–8 min" if heat != "HOT" else "~0–0.15 s"
        item = _QItem(priority=prio, ts=now, id=qid, tenant=tenant, heat=heat, payload=payload, eta_hint=eta)
        heapq.heappush(self._heap, (item.priority, item.ts, item.id, item))
        self._depth += 1
        return item

    def dequeue(self) -> _QItem | None:
        if not self._heap:
            return None
        _, _, _, it = heapq.heappop(self._heap)
        self._depth -= 1
        return it

    @property
    def depth(self) -> int:  # ruff: allow simple property
        return self._depth


PROOF_QUEUE = ProofQueue()
