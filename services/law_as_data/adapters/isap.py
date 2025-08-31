from __future__ import annotations

from dataclasses import dataclass

from ..cache import FileCache, cache_from_uri


@dataclass
class LawDocument:
    uri: str
    digest: str
    path: str


def fetch_and_cache_isap(uri: str, cache: FileCache | None = None) -> LawDocument:
    cs = cache_from_uri(uri, cache)
    return LawDocument(uri=cs.uri, digest=cs.digest, path=str(cs.path))
