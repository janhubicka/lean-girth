#!/usr/bin/env python3
"""Bounded chordless-cycle internal completion diagnostic. NOT a proof.

For cycle lengths 4..9, a bag's trace on the cycle vertices must be
a clique of the induced cycle. Its nonempty cliques are precisely
the cycle's n vertices and n consecutive pairs. Covering all required
consecutive pairs forces all n pair bags to be present; the only extra
allowable original trace bags are subsets of those cliques, namely
optional singleton bags. For every such internal completion candidate,
check that no running-intersection join tree exists.

The necessary and sufficient test for a join tree is maximum possible
sum of pairwise bag intersections = sum over vertices (occurrences-1).
We compute the former using a maximum spanning tree.
"""

def has_join_tree(bags):
    n = len(bags)
    if n <= 1:
        return True
    parents = list(range(n))

    def find(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i

    scored_edges = sorted(
        [
            ((a & b).bit_count(), i, j)
            for i, a in enumerate(bags)
            for j, b in enumerate(bags) if i < j
        ],
        reverse=True,
    )
    total = 0
    for weight, i, j in scored_edges:
        ri, rj = find(i), find(j)
        if ri != rj:
            parents[ri] = rj
            total += weight

    universe = 0
    for bag in bags:
        universe |= bag
    target = sum(
        sum(bool(bag & (1 << v)) for bag in bags) - 1
        for v in range(universe.bit_length())
        if universe & (1 << v)
    )
    return total == target


def cycle_adjacent(n, x, y):
    return x != y and ((x + 1) % n == y or (y + 1) % n == x)


def cross_pair_nonedge(n, e, f):
    endpoints = {e, (e + 1) % n, f, (f + 1) % n}
    return any(
        not cycle_adjacent(n, x, y)
        for x in endpoints for y in endpoints if x != y
    )


def audit(n):
    assert n >= 4
    # Exactly the CrossPairNonedge hypothesis in the Lean adapter.
    assert all(
        cross_pair_nonedge(n, e, f)
        for e in range(n) for f in range(n) if e != f
    )
    # Every cycle vertex belongs to two distinct required edges.
    assert all(
        sum(x in {e, (e + 1) % n} for e in range(n)) == 2
        for x in range(n)
    )
    pairs = [(1 << i) | (1 << ((i + 1) % n)) for i in range(n)]
    singles = [1 << i for i in range(n)]
    checked = completions = 0
    for choice in range(1 << n):
        bags = pairs + [
            single for i, single in enumerate(singles)
            if choice & (1 << i)
        ]
        checked += 1
        if has_join_tree(bags):
            completions += 1
    print(
        f"cycle length={n}, checked completions={checked}, "
        f"valid join trees={completions}"
    )
    assert completions == 0


if __name__ == "__main__":
    # The length-three case is deliberately EXCLUDED: a triangle
    # has a single containing clique bag, and CrossPairNonedge fails.
    assert not cross_pair_nonedge(3, 0, 1)
    assert has_join_tree([(1 << 3) - 1])
    for k in range(4, 10):
        audit(k)
