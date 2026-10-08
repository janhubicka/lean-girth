"""Finite regression tests; these supplement, not replace, the Lean proofs."""
from itertools import combinations, product
import json


def linear(edges):
    return all(len(e & f) <= 1 for e, f in combinations(edges, 2))


def shadow(edges, boundary):
    return frozenset((i, j) for i in boundary for j in boundary
                     if i != j and any(i in e and j in e for e in edges))


left = frozenset((0, 1, 2))
right = frozenset((3, 4, 5))
blocker = frozenset((0, 3, 6))
candidate = frozenset((0, 3, 7))
clear = {left, right}
blocked = clear | {blocker}
assert linear(clear) and linear(blocked)
assert linear(clear | {candidate}) and not linear(blocked | {candidate})
assert (0, 3) not in shadow(clear, range(6))
assert (0, 3) in shadow(blocked, range(6))

# All linear 3-uniform supports with <=4 edges on six vertices.
triples = [frozenset(e) for e in combinations(range(6), 3)]
support_count = attachment_count = 0
states = {}
for n in range(5):
    for E in combinations(triples, n):
        if not linear(E):
            continue
        support_count += 1
        sh = shadow(E, range(4))
        legal = []
        for i, j in combinations(range(4), 2):
            e = frozenset((i, j, 6))  # 6 is genuinely fresh.
            actual = linear((*E, e))
            predicted = (i, j) not in sh
            assert actual == predicted
            legal.append(actual)
            attachment_count += 1
        if sh in states:
            assert states[sh] == tuple(legal)
        states[sh] = tuple(legal)

# Every labelled map from four positions into three host vertices.
functions = list(product(range(3), repeat=4))
subsets = [set(c) for n in range(5) for c in combinations(range(4), n)]


def kernel(f):
    return tuple(f[i] == f[j] for i in range(4) for j in range(4))


groups = {}
for f in functions:
    groups.setdefault(kernel(f), []).append(f)
transport_pairs = carrier_tests = coherence_tests = 0
for fs in groups.values():
    for f in fs:
        for g in fs:
            T = dict(zip(f, g))
            assert len(T) == len(set(f)) == len(set(g))
            assert len(set(T.values())) == len(T)
            transport_pairs += 1
            for S in subsets:
                for R in subsets:
                    fS, fR = {f[i] for i in S}, {f[i] for i in R}
                    gS, gR = {g[i] for i in S}, {g[i] for i in R}
                    assert (fS <= fR) == (gS <= gR)
                    assert (fS == fR) == (gS == gR)
                    carrier_tests += 1
            for h in fs:
                U = dict(zip(g, h))
                V = dict(zip(f, h))
                assert {x: U[T[x]] for x in T} == V
                coherence_tests += 1
report = dict(linear_supports=support_count, fresh_attachment_tests=attachment_count,
              boundary_shadow_types=len(states), semantic_transport_pairs=transport_pairs,
              carrier_comparisons=carrier_tests, composition_checks=coherence_tests,
              external_blocker_counterexample=True, all_passed=True)
print(json.dumps(report, indent=2))
