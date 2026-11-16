#!/usr/bin/env python3
"""Bounded cycle-certificate diagnostic, NOT a proof.

A chordless cycle of length k>=4 has k distinct unordered edges,
is triangle-free on its cycle vertices, and therefore supplies a
nonadjacent pair among the endpoints of any two different edges.

This exactly tests the *simpler* new Lean interfaces
distinct_two_pairs_have_third and crossPairNonedge_of_induced_cliqueFree.
It is deliberately separate from the expensive join-tree completion
test, so lengths through 100 can be checked.
"""
from itertools import combinations


def cycle_adj(k, a, b):
    return a != b and (a - b) % k in (1, k - 1)


def check(k):
    pairs = [frozenset((i, (i + 1) % k)) for i in range(k)]
    assert len(set(pairs)) == k
    # No three vertices induce a triangle on the cycle.
    assert not any(
        cycle_adj(k, a, b) and cycle_adj(k, a, c)
        and cycle_adj(k, b, c)
        for a, b, c in combinations(range(k), 3)
    )
    for i, j in combinations(range(k), 2):
        first, second = pairs[i], pairs[j]
        # Exact "third endpoint of the second edge" witness.
        assert second - first
        # Exact CrossPairNonedge consequence without choosing
        # a separate Lean witness for each pair of cycle edges.
        assert any(
            not cycle_adj(k, x, y)
            for x, y in combinations(first | second, 2)
        )


if __name__ == "__main__":
    # Triangle negative control. These properties must NOT hold at k=3.
    assert all(cycle_adj(3, a, b) for a, b in combinations(range(3), 2))
    for k in range(4, 101):
        check(k)
    print("PASS: 97 cycle lengths (4..100), edge distinctness, "
          "triangle exclusion and cross-pair witnesses")
