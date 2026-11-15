#!/usr/bin/env python3
"""Exhaustive direct PEO maximal-clique count on graphs n<=6 (NOT a proof)."""
from itertools import combinations

def peo(G):
    rest, order = set(range(len(G))), []
    while rest:
        simplicial = [v for v in sorted(rest) if all(
            y in G[x] for x, y in combinations(sorted(G[v] & rest), 2))]
        if not simplicial:
            return None
        v = simplicial[0]
        order.append(v)
        rest.remove(v)
    return order

def maximal_cliques(G):
    n, cliques = len(G), []
    for bits in range(1, 1 << n):
        S = {i for i in range(n) if bits & (1 << i)}
        if all(v in G[u] for u, v in combinations(sorted(S), 2)):
            cliques.append(S)
    return [S for S in cliques if not any(S < T for T in cliques)]

def audit(n):
    edges = list(combinations(range(n), 2))
    valid = invalid = total_max = 0
    for mask in range(1 << len(edges)):
        G = [set() for _ in range(n)]
        for bit, (u, v) in enumerate(edges):
            if mask & (1 << bit):
                G[u].add(v)
                G[v].add(u)
        order = peo(G)
        if order is None:
            invalid += 1
            continue
        valid += 1
        rank = {v: i for i, v in enumerate(order)}
        maxes = maximal_cliques(G)
        first_vertices = []
        for K in maxes:
            first = min(K, key=rank.__getitem__)
            bag = {first} | {w for w in G[first] if rank[w] > rank[first]}
            assert bag == K, (n, mask, order, K, bag)
            first_vertices.append(first)
        assert len(set(first_vertices)) == len(maxes) <= n
        total_max += len(maxes)
    print(f"n={n}: chordal={valid}, nonchordal={invalid}, maximal_cliques_total={total_max}")
    return valid

if __name__ == "__main__":
    for n in range(7):
        num = audit(n)
    assert num == 18154
