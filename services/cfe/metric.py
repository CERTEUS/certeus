#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/cfe/metric.py                              |
# | ROLE: Project module.                                       |
# | PLIK: services/cfe/metric.py                              |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Metryka CFE i krzywizny Ricciego (lekka aproksymacja Olliviera na grafie).

EN: CFE metric and Ricci curvatures (lightweight Ollivier approximation on a graph).

Założenia i cele W1:
- Realna (deterministyczna) metryka grafowa budowana z ziarna `case_id`.
- Szybkość: obliczenia poniżej ~10 ms na zapytanie i p95 < 200 ms dla API.
- Brak zewnętrznych ciężkich zależności (czysty Python, małe grafy, cache).

Podejście (skrót):
- Generujemy niewielki graf „prawny” (małe-world/trójkąty → dodatnie krzywizny,
  łańcuchy → ujemne/zerowe). Wielkość ~24–36 węzłów.
- Aproksymujemy krzywiznę Olliviera dla krawędzi (u, v):
    kappa(u,v) ≈ 1 - \bar{W1}(μ_u, μ_v), gdzie \bar{W1} to uśredniony minimalny
    dystans pomiędzy sąsiadami u oraz v (heurystyka transportu 1‑Wass.).
  Heurystyka jest szybka i stabilna dla małych grafów; zapewnia „realne”
  zróżnicowanie znaków krzywizny.

Wynik publikujemy jako `kappa_max` (przycięty do [0,1] i dolny próg 0.005,
aby UI miało sensowną skalę nawet dla grafów z przewagą krzywizn ≤ 0).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import os
import random
import time

# === KONFIGURACJA / CONFIGURATION ===
_DEFAULT_NODES = 28
_SEED_FALLBACK = 0xCFEA2


# === MODELE / MODELS ===


@dataclass(frozen=True)
class CurvatureSummary:
    """PL: Agregat wyników CFE (tu: maksymalna krzywizna). EN: Result summary."""

    kappa_max: float


# === LOGIKA / LOGIC ===


class Graph:
    def __init__(self, n: int) -> None:
        self.n = n
        self.adj: dict[int, list[int]] = {i: [] for i in range(n)}

    def add_edge(self, u: int, v: int) -> None:
        if v not in self.adj[u]:
            self.adj[u].append(v)
        if u not in self.adj[v]:
            self.adj[v].append(u)

    def neighbors(self, u: int) -> list[int]:
        return self.adj.get(u, [])

    def bfs_path(self, src: int, dst: int) -> list[int]:
        """Najkrótsza ścieżka (węzły) między src a dst metodą BFS."""
        if src == dst:
            return [src]
        from collections import deque

        q = deque([src])
        prev: dict[int, int] = {src: -1}
        while q:
            u = q.popleft()
            for v in self.neighbors(u):
                if v in prev:
                    continue
                prev[v] = u
                if v == dst:
                    path = [v]
                    while path[-1] != src:
                        path.append(prev[path[-1]])
                    path.reverse()
                    return path
                q.append(v)
        return []

    def astar_path_and_action(self, src: int, dst: int) -> tuple[list[int], float]:
        """A*: koszt krawędzi = 1 + (1 - kappa(u,v)); heurystyka: odległość po pierścieniu."""
        import heapq

        def h(u: int) -> float:
            d = abs(dst - u)
            return float(min(d, self.n - d))

        open_q: list[tuple[float, int]] = [(h(src), src)]
        came_from: dict[int, int] = {src: -1}
        g_score: dict[int, float] = {src: 0.0}

        while open_q:
            _, u = heapq.heappop(open_q)
            if u == dst:
                path = [u]
                while path[-1] != src:
                    path.append(came_from[path[-1]])
                path.reverse()
                return path, float(round(g_score[dst], 3))

            for v in self.neighbors(u):
                k = _approx_ollivier_kappa(self, u, v)
                w = 1.0 + (1.0 - k)
                tentative = g_score[u] + w
                if tentative < g_score.get(v, float("inf")):
                    came_from[v] = u
                    g_score[v] = tentative
                    f_score = tentative + h(v)
                    heapq.heappush(open_q, (f_score, v))
        return [], float("inf")


def _seed_from_case(case_id: str | None) -> int:
    if not case_id:
        return _SEED_FALLBACK
    h = hashlib.sha256(case_id.encode("utf-8")).digest()
    return int.from_bytes(h[:8], "big") ^ _SEED_FALLBACK


def _build_legal_smallworld(n: int, seed: int) -> Graph:
    """Zbuduj niewielki graf: pierścień + losowe chordy + kilka trójkątów.

    Zapewnia dodatnie i ujemne krzywizny; deterministyczny dla `seed`.
    """

    rng = random.Random(seed)
    g = Graph(n)

    # Pierścień (spójność)
    for i in range(n):
        g.add_edge(i, (i + 1) % n)

    # Chordy (mały świat)
    m = max(3, n // 4)
    for _ in range(m):
        u = rng.randrange(n)
        v = (u + rng.randrange(3, n // 2)) % n
        g.add_edge(u, v)

    # Kilka trójkątów (dodatnie krzywizny)
    t = max(2, n // 10)
    for _ in range(t):
        a = rng.randrange(n)
        b = (a + 2 + rng.randrange(0, 5)) % n
        c = (b + 2 + rng.randrange(0, 5)) % n
        g.add_edge(a, b)
        g.add_edge(b, c)
        g.add_edge(a, c)

    return g


@lru_cache(maxsize=256)
def _graph_for_case_inner(case_id: str | None, epoch_key: int) -> Graph:
    seed = _seed_from_case(case_id)
    return _build_legal_smallworld(n=_DEFAULT_NODES, seed=seed)


def _graph_for_case(case_id: str | None) -> Graph:
    """Zwróć graf dla case_id z TTL cache sterowanym ENV `CFE_CACHE_TTL_SEC`.

    TTL<=0 oznacza cache bezterminowy (pojedynczy `epoch_key=0`).
    """
    try:
        ttl = int(os.getenv("CFE_CACHE_TTL_SEC", "300") or "0")
    except Exception:
        ttl = 300
    epoch_key = int(time.time() // max(1, ttl)) if ttl > 0 else 0
    return _graph_for_case_inner(case_id, epoch_key)


def _bfs_dist(g: Graph, src: int, targets: Iterable[int]) -> int:
    """Najmniejsza odległość od `src` do któregokolwiek z `targets` (BFS)."""
    target_set = set(targets)
    if src in target_set:
        return 0
    seen = {src}
    frontier = [src]
    d = 0
    while frontier:
        d += 1
        nxt: list[int] = []
        for u in frontier:
            for v in g.neighbors(u):
                if v in target_set:
                    return d
                if v not in seen:
                    seen.add(v)
                    nxt.append(v)
        frontier = nxt
        if d > g.n:  # guard (teoretycznie nieosiągalne dla spójnego grafu)
            break
    return g.n  # brak ścieżki (nie powinno się zdarzyć)


def _approx_ollivier_kappa(g: Graph, u: int, v: int) -> float:
    """Heurystyczna aproksymacja kappa(u,v) w duchu Olliviera.

    μ_u – rozkład jednostajny na sąsiadach u; μ_v – analogicznie dla v.
    W1 ~ średnia z minimalnych odległości od każdego sąsiada u do zbioru
    sąsiadów v (transport „najbliższego sąsiada”). Zwracamy 1 - W1_norm.
    """

    Nu = g.neighbors(u)
    Nv = g.neighbors(v)
    if not Nu or not Nv:
        return 0.0
    dists = []
    for a in Nu:
        d_ab = _bfs_dist(g, a, Nv)
        dists.append(float(d_ab))
    # Normalizacja: typowe odległości 1–3 → skala [0,1] przez 1 + mean
    mean_d = sum(dists) / max(1, len(dists))
    w1_norm = mean_d / (1.0 + mean_d)
    kappa = 1.0 - w1_norm
    # Przytnij do [0,1] dla stabilności UI i metryk
    if kappa < 0.0:
        return 0.0
    if kappa > 1.0:
        return 1.0
    return kappa


def _kappa_max(g: Graph) -> float:
    kmax = 0.0
    for u in range(g.n):
        for v in g.neighbors(u):
            if v < u:  # liczymy każdą krawędź raz
                continue
            k = _approx_ollivier_kappa(g, u, v)
            if k > kmax:
                kmax = k
    # Dolny próg (żeby UI nie miało zera i heatmapa nie zgasła całkiem)
    return max(0.005, float(kmax))


@lru_cache(maxsize=128)
def kappa_max_for_case(case_id: str | None) -> CurvatureSummary:
    """Zwraca podsumowanie krzywizn dla danego `case_id` (z cache).

    Deterministyczny wynik dla danego `case_id` (seed → topologia grafu).
    Czas: ~1–5 ms dla n≈28 (lokalnie), wielokrotne wywołania → LRU cache.
    """

    g = _graph_for_case(case_id)
    kmax = _kappa_max(g)
    return CurvatureSummary(kappa_max=round(kmax, 3))


def geodesic_for_case(case_id: str | None) -> tuple[list[str], float]:
    """Geodezyjna ścieżka i akcja na grafie case (deterministycznie per case_id)."""
    g = _graph_for_case(case_id)
    seed = _seed_from_case(case_id)
    src = int(seed % g.n)
    dst = int((src + (g.n // 2)) % g.n)
    idx_path, action = g.astar_path_and_action(src, dst)
    if not idx_path:
        idx_path = g.bfs_path(src, dst) or [src]
        action = float(len(idx_path) - 1)
    names = [f"n{i}" for i in idx_path]
    return names, float(round(action, 3))


def horizon_mass_for_case(case_id: str | None) -> float:
    """Masa horyzontu z uśrednionej penalizacji (1-kappa) na geodezyjnej."""
    g = _graph_for_case(case_id)
    seed = _seed_from_case(case_id)
    src = int(seed % g.n)
    dst = int((src + (g.n // 2)) % g.n)
    path, _ = g.astar_path_and_action(src, dst)
    if not path:
        return 0.15
    penalties: list[float] = []
    for i in range(len(path) - 1):
        u, v = path[i], path[i + 1]
        k = _approx_ollivier_kappa(g, u, v)
        penalties.append(max(0.0, 1.0 - k))
    avg_pen = (sum(penalties) / len(penalties)) if penalties else 0.0
    mass = 0.1 + 0.6 * avg_pen
    return float(round(max(0.05, min(0.95, mass)), 3))


def lensing_map_for_case(case_id: str | None) -> dict[str, float]:
    """Deterministyczna, lekka mapa lensingu precedensów (2–3 klucze)."""
    rng = random.Random(_seed_from_case(case_id) ^ 0xA5A5)
    keys = [
        f"precedent:K_{2000 + rng.randrange(0, 30)}",
        f"precedent:III_{2010 + rng.randrange(0, 14)}",
    ]
    weights = [0.3 + 0.4 * rng.random(), 0.2 + 0.3 * rng.random()]
    if rng.random() > 0.6:
        keys.append(f"precedent:SN_{1990 + rng.randrange(0, 35)}")
        weights.append(0.1 + 0.2 * rng.random())
    total = sum(weights) or 1.0
    return {k: float(round(w / total, 3)) for k, w in zip(keys, weights, strict=False)}


# === I/O / ENDPOINTS ===

# (używane przez router API)


# === TESTY / TESTS ===
