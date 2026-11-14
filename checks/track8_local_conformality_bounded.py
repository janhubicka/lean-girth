#!/usr/bin/env python3
"""Exhaustively test the missing-face local-conformality obstruction, n<=4.

For each cover by distinct nonempty subsets of [n], find a smallest clique
not contained in any original bag. Choose one original bag containing
each vertex-deletion face. Assert that NO completion of those chosen
ORIGINAL bags inside the cover admits a join tree.

A maximum-weight spanning tree (weights = intersection sizes) checks the
running-intersection property. This is bounded evidence, NOT a proof.
"""
from collections import Counter


def has_join_tree(bags):
    n = len(bags)
    if n <= 1:
        return True
    edges = sorted(
        ((a & b).bit_count(), i, j)
        for i, a in enumerate(bags)
        for j, b in enumerate(bags) if i < j
    , reverse=True)
    parents = list(range(n))

    def root(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i

    total = 0
    for weight, i, j in edges:
        u, v = root(i), root(j)
        if u != v:
            parents[u] = v
            total += weight
    universe = 0
    for bag in bags:
        universe |= bag
    required = sum(
        sum(bool(bag & (1 << v)) for bag in bags) - 1
        for v in range(universe.bit_length()) if universe & (1 << v)
    )
    return total == required


def audit(n):
    subsets = tuple(range(1, 1 << n))
    m = len(subsets)
    join = [False] * (1 << m)
    for family_mask in range(1, 1 << m):
        family = [subsets[i] for i in range(m) if family_mask & (1 << i)]
        join[family_mask] = has_join_tree(family)

    covers = nonconformal = witnesses = invalid_extensions = 0
    sizes = Counter()
    for family_mask in range(1, 1 << m):
        indices = [i for i in range(m) if family_mask & (1 << i)]
        if any(
            not any(subsets[i] & (1 << v) for i in indices)
            for v in range(n)
        ):
            continue
        covers += 1
        uncovered = []
        for K in range(1, 1 << n):
            if not all(
                any(
                    subsets[i] & (1 << x) and subsets[i] & (1 << y)
                    for i in indices
                )
                for x in range(n) for y in range(x + 1, n)
                if K & (1 << x) and K & (1 << y)
            ):
                continue
            if not any((subsets[i] & K) == K for i in indices):
                uncovered.append(K)
        if not uncovered:
            continue
        nonconformal += 1
        K = min(uncovered, key=int.bit_count)
        sizes[K.bit_count()] += 1
        selected = 0
        for v in range(n):
            if not K & (1 << v):
                continue
            face = K & ~(1 << v)
            candidates = [
                i for i in indices if (subsets[i] & face) == face
            ]
            assert candidates, "A smallest uncovered clique has uncovered face"
            selected |= 1 << candidates[0]
        assert selected.bit_count() <= n
        witnesses += 1
        S = family_mask
        while S:
            if (S & selected) == selected and join[S]:
                invalid_extensions += 1
                break
            S = (S - 1) & family_mask

    print(
        f"n={n}, covers={covers}, nonconformal={nonconformal}, "
        f"face_obstructions={witnesses}, false_extensions={invalid_extensions}, "
        f"clique_sizes={dict(sorted(sizes.items()))}"
    )
    assert invalid_extensions == 0


if __name__ == "__main__":
    for n in range(1, 5):
        audit(n)
