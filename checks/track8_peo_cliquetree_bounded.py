#!/usr/bin/env python3
"""Exhaustive diagnostic: PEO parent-forest clique trees, n <= 6 (NOT a proof).

For every graph on n labelled vertices, greedily remove a simplicial
vertex when possible. Given the resulting perfect elimination order:
  * construct the bag at v from v plus its later neighbours;
  * join v to its least later neighbour, connecting component roots;
  * check running intersections for every vertex;
  * delete each proper subbag or duplicate by star-rewiring the deleted
    node's neighbours through the component of a containing bag;
  * compare the surviving bag sets with all maximal graph cliques.

This checks disconnected cases and all intermediate join trees.
"""
from collections import Counter


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def connected(adj, S):
    if not S:
        return True
    start = next(iter(S))
    found, todo = {start}, [start]
    while todo:
        v = todo.pop()
        for w in adj[v] & S:
            if w not in found:
                found.add(w)
                todo.append(w)
    return found == S


def greedy_peo(G):
    remaining, order = set(range(len(G))), []
    while remaining:
        possible = [
            v for v in remaining
            if all(
                (G[v] & remaining) - {w} <= G[w]
                for w in G[v] & remaining
            )
        ]
        if not possible:
            return None
        v = min(possible)
        order.append(v)
        remaining.remove(v)
    return order


def maximal_cliques(G):
    found = []
    for mask in range(1, 1 << len(G)):
        S = set(vertices(mask))
        if all(S - {v} <= G[v] for v in S):
            found.append(mask)
    return {
        mask for mask in found
        if not any(mask != big and mask & big == mask for big in found)
    }


def check_tree(bags, adj, n):
    assert bags.keys() == adj.keys()
    if not bags:
        return
    assert all(v not in neigh for v, neigh in adj.items())
    assert all(v in adj[w] for w, neigh in adj.items() for v in neigh)
    assert sum(map(len, adj.values())) == 2 * (len(adj) - 1)
    assert connected(adj, set(adj))
    for x in range(n):
        occur = {v for v, bag in bags.items() if bag & (1 << x)}
        assert connected(adj, occur)


def check_graph(G, order):
    n = len(G)
    bags, parent = {}, {}
    for i, v in enumerate(order):
        later = set(order[i + 1:])
        neigh = G[v] & later
        bags[v] = (1 << v) | sum(1 << w for w in neigh)
        if neigh:
            p = min(neigh, key=order.index)
            parent[v] = p
            assert order.index(v) < order.index(p)
    for v, p in parent.items():
        assert (bags[v] & ~(1 << v)) & ~bags[p] == 0

    adj = {v: set() for v in bags}
    for v, p in parent.items():
        adj[v].add(p)
        adj[p].add(v)

    # The directed parent links are strictly increasing.
    components, unseen = [], set(adj)
    while unseen:
        seen = {next(iter(unseen))}
        todo = list(seen)
        while todo:
            a = todo.pop()
            for b in adj[a]:
                if b not in seen:
                    seen.add(b)
                    todo.append(b)
        components.append(seen)
        unseen -= seen

    roots = [next(v for v in comp if v not in parent) for comp in components]
    for a, b in zip(roots, roots[1:]):
        adj[a].add(b)
        adj[b].add(a)
    check_tree(bags, adj, n)

    while True:
        redundant = [
            (v, w) for v in bags for w in bags
            if v != w and bags[v] & bags[w] == bags[v]
            and (bags[v] != bags[w] or v > w)
        ]
        if not redundant:
            break
        v, hub_bag = redundant[0]
        neigh = set(adj[v])
        assert neigh
        for a in neigh:
            adj[a].remove(v)
        del adj[v]
        del bags[v]

        # Find the component of the containing hub bag after deletion.
        def reaches(a, b):
            seen, todo = {a}, [a]
            while todo:
                u = todo.pop()
                for z in adj[u]:
                    if z not in seen:
                        seen.add(z)
                        todo.append(z)
            return b in seen

        hub = next(a for a in neigh if reaches(a, hub_bag))
        for a in neigh - {hub}:
            adj[a].add(hub)
            adj[hub].add(a)
        check_tree(bags, adj, n)

    assert set(bags.values()) == maximal_cliques(G)
    return len(components), len(bags)


def audit(max_n=6):
    for n in range(max_n + 1):
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
        counts = Counter()
        for mask in range(1 << len(edges)):
            G = [set() for _ in range(n)]
            for bit, (i, j) in enumerate(edges):
                if mask & (1 << bit):
                    G[i].add(j)
                    G[j].add(i)
            order = greedy_peo(G)
            if order is None:
                counts["nonchordal"] += 1
                continue
            component_count, num_max = check_graph(G, order)
            counts["chordal"] += 1
            counts["disconnected_parent_forest"] += component_count > 1
            counts["total_maximal_cliques"] += num_max
        print(f"n={n}: {dict(counts)}", flush=True)
    # Known labelled six-vertex chordal graph count is a regression gate.
    assert counts["chordal"] == 18154


if __name__ == "__main__":
    audit()
