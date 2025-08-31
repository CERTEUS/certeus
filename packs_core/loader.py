from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Protocol


@dataclass(slots=True)
class PackInfo:
    name: str
    abi: str
    caps: list[str]


class PackLike(Protocol):
    def handle(self, kind: str, payload: dict[str, Any]) -> Any: ...


def discover() -> list[PackInfo]:
    """
    Minimalna implementacja na potrzeby edytora i API listującego paczki.
    Zwraca pustą listę (MVP); realna implementacja może skanować katalogi `plugins/`.
    """
    return []


def load(path: str) -> PackLike:  # noqa: A002 - zgodność z istniejącymi importami
    """
    Ładowanie paczki po ścieżce/identyfikatorze.
    Tu stub rzuca NotImplementedError, by nie maskować błędów wykonania.
    """
    raise NotImplementedError(f"Pack loader is not implemented for: {path}")

