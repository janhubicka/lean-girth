#!/usr/bin/env python3
"""Exhaustive finite checks of the physical edge-token split, NOT a Lean proof.

Enumerate all edge carriers on <=6 labelled vertices, all binary predicate
assignments, and every allowed predicate set. Each pair of distinct physical
edges is checked for image injectivity and absence of forbidden intersections.
"""
from itertools import combinations, product
import json


def main():
    tally = dict(
        vertices=0, predicate_cases=0, edge_cases=0,
        distinct_edge_pair_checks=0, carrier_projection_checks=0,
        split_embedding_checks=0, isolated_lift_checks=0,
    )
    for n in range(2, 7):
        verts = tuple(range(n))
        carriers = [
            frozenset(a)
            for size in range(2, n + 1)
            for a in combinations(verts, size)
        ]
        tally["vertices"] += n
        for part in product((0, 1), repeat=n):
            for allowmask in range(4):
                allowed = {i for i in range(2) if allowmask & (1 << i)}
                tally["predicate_cases"] += 1

                def lift(e, x):
                    return ("old", x) if part[x] in allowed else ("edge", x, e)

                def projected(z):
                    return z[1]

                images = {
                    e: frozenset(lift(e, x) for x in e)
                    for e in carriers
                }
                assert len(set(images.values())) == len(carriers)
                for e in carriers:
                    assert {projected(z) for z in images[e]} == e
                    assert len(images[e]) == len(e)
                    tally["carrier_projection_checks"] += 1
                    tally["split_embedding_checks"] += 1

                isolated = {
                    x: ("old", x) if part[x] in allowed else ("isolated", x)
                    for x in verts
                }
                assert len(set(isolated.values())) == n
                assert {projected(z) for z in isolated.values()} == set(verts)
                tally["isolated_lift_checks"] += n

                for e, f in combinations(carriers, 2):
                    common = images[e] & images[f]
                    assert all(
                        z[0] == "old" and part[z[1]] in allowed
                        for z in common
                    )
                    tally["distinct_edge_pair_checks"] += 1
                tally["edge_cases"] += len(carriers)

    print(json.dumps({"status": "passed", "scope": __doc__.strip(),
                      "counts": tally}, indent=2))


if __name__ == "__main__":
    main()
