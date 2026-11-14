#!/usr/bin/env python3
"""Independent bounded test of the leaf-private charging theorem (NOT a proof).

Enumerate every nonempty inclusion-antichain of nonempty subsets of an
n-point universe, for n <= 4.  Keep families with a running-intersection
join tree and verify they admit an injective system of representatives.
"""
from itertools import combinations

from track8_small_traces_bounded import has_join_tree


def admits_distinct_representatives(bags, n):
    supports = [
        tuple(i for i in range(n) if bag & (1 << i))
        for bag in bags
    ]
    supports.sort(key=len)

    def search(k, used):
        if k == len(supports):
            return True
        return any(
            not (used & (1 << x)) and search(k + 1, used | (1 << x))
            for x in supports[k]
        )

    return search(0, 0)


def audit(n):
    nonempty = range(1, 1 << n)
    antichains = join_tree_antichains = counterexamples = 0
    for k in range(1, len(nonempty) + 1):
        for family in combinations(nonempty, k):
            if any(
                (a & b) == a or (a & b) == b
                for a, b in combinations(family, 2)
            ):
                continue
            antichains += 1
            if not has_join_tree(family):
                continue
            join_tree_antichains += 1
            if not admits_distinct_representatives(family, n):
                counterexamples += 1

    print(
        f"n={n}, antichains={antichains}, "
        f"join-tree antichains={join_tree_antichains}, "
        f"matching counterexamples={counterexamples}"
    )
    assert counterexamples == 0


if __name__ == "__main__":
    for size in range(1, 5):
        audit(size)
