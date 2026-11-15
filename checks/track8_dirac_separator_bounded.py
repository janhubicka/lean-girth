#!/usr/bin/env python3
"""Bounded diagnostic of minimal clique-separator induction for Dirac's theorem.

Checks all simple graphs on up to six labelled vertices. Not a proof.
"""

from itertools import combinations
from collections import Counter


def components(G, rest):
    todo = set(rest)
    comps = []
    while todo:
        root = next(iter(todo))
        seen = {root}
        frontier = [root]
        while frontier:
            x = frontier.pop()
            for y in G[x] & todo:
                if y not in seen:
                    seen.add(y)
                    frontier.append(y)
        todo.difference_update(seen)
        comps.append(seen)
    return comps


def connected_in(G, a, b, rest):
    return any({a, b} <= C for C in components(G, rest))


def simplicial(G, v, S):
    neigh = G[v] & S
    return all(w in G[u] for u, w in combinations(sorted(neigh), 2))


def chordal(G):
    S = set(range(len(G)))
    while S:
        v = next((v for v in sorted(S) if simplicial(G, v, S)), None)
        if v is None:
            return False
        S.remove(v)
    return True


def is_clique(G, S):
    return all(w in G[u] for u, w in combinations(sorted(S), 2))


def minimal_separator(G, a, b):
    V = set(range(len(G)))
    assert b not in G[a]
    S = V - {a, b}
    assert not connected_in(G, a, b, V - S)
    for s in sorted(tuple(S)):
        if not connected_in(G, a, b, V - (S - {s})):
            S.remove(s)
    assert not connected_in(G, a, b, V - S)
    assert all(connected_in(G, a, b, V - (S - {s})) for s in S)
    return S


def audit(n):
    edges = list(combinations(range(n), 2))
    stats = Counter()
    for mask in range(1 << len(edges)):
        G = [set() for _ in range(n)]
        for i, (u, v) in enumerate(edges):
            if mask >> i & 1:
                G[u].add(v)
                G[v].add(u)
        if not chordal(G):
            stats["nonchordal"] += 1
            continue
        stats["chordal"] += 1
        V = set(range(n))
        simp = {v for v in V if simplicial(G, v, V)}
        assert simp, "simplicial vertex failure"
        nonedges = [(a, b) for a, b in edges if b not in G[a]]
        if not nonedges:
            stats["complete"] += 1
            continue
        stats["noncomplete"] += 1
        assert any(b not in G[a] for a, b in combinations(sorted(simp), 2))
        a, b = nonedges[0]
        S = minimal_separator(G, a, b)
        assert is_clique(G, S), "nonclique minimal separator"
        stats["separator_clique"] += 1
        parts = components(G, V - S)
        A = next(C for C in parts if a in C)
        B = next(C for C in parts if b in C)
        assert A != B and not (A & B)
        assert all(G[s] & A and G[s] & B for s in S)
        picked = []
        for C in (A, B):
            T = C | S
            if is_clique(G, T):
                w = next(iter(C))
            else:
                candidates = [w for w in T if simplicial(G, w, T)]
                assert any(y not in G[x] for x, y in combinations(candidates, 2))
                w = next(w for w in candidates if w in C)
            assert simplicial(G, w, T)
            assert simplicial(G, w, V)
            picked.append(w)
        assert picked[1] not in G[picked[0]]
        stats["inductive_two_simplicial"] += 1
    print(f"n={n}: {dict(stats)}", flush=True)
    return stats


if __name__ == "__main__":
    for n in range(1, 7):
        stats = audit(n)
    assert stats["chordal"] == 18154
