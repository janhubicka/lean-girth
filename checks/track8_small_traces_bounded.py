#!/usr/bin/env python3
"""Bounded diagnostic, NOT a proof: trace-cover bound versus local join trees.

For each n<=4, enumerate all finite covers by distinct nonempty subsets of
the n-point universe.  For covers with more than n distinct maximal traces,
find a selected family of <=max(2,n) members with no join-tree completion
inside that cover.

A family admits a join tree precisely when a maximum-weight spanning tree
with edge weights |F_i intersect F_j| attains sum_x (occurrences(x)-1).
The latter equality says every vertex's occurrence nodes are connected.
"""
from collections import Counter


def has_join_tree(bags):
    k = len(bags)
    if k <= 1:
        return True
    parent = list(range(k))

    def find(x):
        while x != parent[x]:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    edges = sorted(
        ((a & b).bit_count(), i, j)
        for i, a in enumerate(bags)
        for j, b in enumerate(bags)
        if i < j
    )
    edges.reverse()
    total = 0
    for weight, i, j in edges:
        ri, rj = find(i), find(j)
        if ri != rj:
            parent[ri] = rj
            total += weight

    universe = 0
    for bag in bags:
        universe |= bag
    bound = sum(
        sum(bool(bag & (1 << x)) for bag in bags) - 1
        for x in range(universe.bit_length())
        if universe & (1 << x)
    )
    return total == bound


def min_failed_selection_size(family, n):
    m = len(family)
    good = [
        has_join_tree([family[i] for i in range(m) if mask & (1 << i)])
        for mask in range(1 << m)
    ]
    # Subset DP: after this, good[mask] means some allowable join-tree
    # completion of the members marked by mask exists inside family.
    for i in range(m):
        for mask in range(1 << m):
            if not mask & (1 << i):
                good[mask] |= good[mask | (1 << i)]
    failed = [
        mask for mask in range(1 << m)
        if mask.bit_count() <= max(2, n) and not good[mask]
    ]
    return min((mask.bit_count() for mask in failed), default=None)


def check(n):
    subsets = tuple(range(1, 1 << n))
    too_many = unexpected = 0
    obstruction_size = Counter()
    for mask in range(1 << len(subsets)):
        family = tuple(
            subsets[i] for i in range(len(subsets)) if mask & (1 << i)
        )
        if not all(
            any(bag & (1 << x) for bag in family) for x in range(n)
        ):
            continue  # Not a cover.
        maximal = tuple(
            bag for bag in family if not any(
                bag != other and bag & other == bag for other in family
            )
        )
        if len(maximal) <= n:
            continue
        too_many += 1
        size = min_failed_selection_size(family, n)
        if size is None:
            unexpected += 1
        else:
            obstruction_size[size] += 1

    print(
        f"n={n}: covers with >n maximal traces={too_many}, "
        f"locally extendible counterexamples={unexpected}, "
        f"obstruction sizes={dict(sorted(obstruction_size.items()))}"
    )
    assert unexpected == 0


if __name__ == "__main__":
    for n in range(1, 5):
        check(n)
