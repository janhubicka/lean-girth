#!/usr/bin/env python3
"""Finite adversarial regression for Path A's two-cut isolated-owner lemma.

A cyclic owner-change position is t when owner[t] != owner[(t+1) mod n].
An isolated occurrence p has owner[p] different from BOTH neighboring
owners. For n>=3 and exactly two cyclic owner changes, there can be at
most ONE isolated occurrence. The Lean theorem proves this for all n
and arbitrary owner types; this exhaustive small check only guards
the finite orientation and wrap cases.
"""
from itertools import product


def run(max_n: int = 9, alphabet: int = 3) -> None:
    total = 0
    zero = 0
    one = 0
    for n in range(3, max_n + 1):
        for owner in product(range(alphabet), repeat=n):
            cuts = [
                t for t in range(n)
                if owner[t] != owner[(t + 1) % n]
            ]
            if len(cuts) != 2:
                continue
            total += 1
            isolated = [
                t for t in range(n)
                if owner[(t - 1) % n] != owner[t]
                and owner[t] != owner[(t + 1) % n]
            ]
            assert len(isolated) <= 1, (n, owner, cuts, isolated)
            if not isolated:
                zero += 1
            else:
                one += 1
    assert total == zero + one and one > 0 and zero > 0
    print(f"PASS: {total} two-cut words, {zero} without isolated positions, "
          f"{one} with exactly one, no counterexample (3..{max_n})")


if __name__ == "__main__":
    run()
