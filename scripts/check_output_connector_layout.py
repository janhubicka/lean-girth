#!/usr/bin/env python3
"""Finite adversarial regression for source/output cyclic connector layout.

A replacement block keeps its old connector at the END. Short/kept
blocks contribute one connector; a long block contributes one fresh
wagon immediately before the old connector. LongValid requires both
the previous and current ORIGINAL boundaries to be vertex connectors.

Checks source-wagon and fresh-wagon immediate neighbour equations,
and that every split between successive oldPos entries is precisely
caused by the next block's long-piece wagon. Includes cyclic wrap and
length-two cases. FINITE REGRESSION ONLY, NOT A LEAN PROOF.
"""
from itertools import product
import json

def check():
    results = {
        "configurations": 0, "valid": 0, "old_wagon_checks": 0,
        "fresh_wagon_checks": 0, "split_checks": 0, "negative_controls": {},
    }
    for n in range(2, 8):
        for mask in range(1 << n):
            old = [
                ("wagon" if (mask >> i) & 1 else "vertex", i)
                for i in range(n)
            ]
            for state in product(range(3), repeat=n):
                # 0 = keep, 1 = short, 2 = long
                results["configurations"] += 1
                if any(
                    state[i] == 2
                    and (old[i][0] != "vertex"
                         or old[(i - 1) % n][0] != "vertex")
                    for i in range(n)
                ):
                    continue
                results["valid"] += 1
                blocks = [
                    ([("fresh", i), old[i]] if state[i] == 2 else [old[i]])
                    for i in range(n)
                ]
                output = [a for block in blocks for a in block]
                old_pos = [output.index(a) for a in old]

                assert len(set(output)) == len(output)
                for j, w in enumerate(output):
                    prev = output[(j - 1) % len(output)]
                    succ = output[(j + 1) % len(output)]
                    if w[0] == "wagon":
                        i = w[1]
                        assert prev == old[(i - 1) % n]
                        assert succ == old[(i + 1) % n]
                        results["old_wagon_checks"] += 1
                    elif w[0] == "fresh":
                        i = w[1]
                        assert state[i] == 2
                        assert prev == old[(i - 1) % n]
                        assert succ == old[i]
                        results["fresh_wagon_checks"] += 1

                for i in range(n):
                    k = (i + 1) % n
                    if old_pos[k] != (old_pos[i] + 1) % len(output):
                        assert state[k] == 2
                        assert output[(old_pos[i] + 1) % len(output)] == ("fresh", k)
                        results["split_checks"] += 1

    # Dropping the vertex-boundary requirement can insert a wagon
    # immediately beside an inherited source wagon: old neighbours
    # are then NOT preserved.
    bad_old = [("wagon", 0), ("vertex", 1), ("vertex", 2)]
    bad_output = [bad_old[0], ("fresh", 1), bad_old[1], bad_old[2]]
    assert bad_output[1] != bad_old[1]
    results["negative_controls"]["allowing_long_beside_old_wagon_breaks_adjacency"] = True

    # Dropping freshness can make a purported new wagon identical with
    # an inherited wagon: no connector-injective output cycle exists.
    bad_output = [("wagon", 0), ("wagon", 0), ("vertex", 1)]
    assert len(set(bad_output)) < len(bad_output)
    results["negative_controls"]["reusing_old_wagon_breaks_connector_injectivity"] = True

    assert results["configurations"] == 335916, results
    assert results["valid"] == 52628, results
    assert results["old_wagon_checks"] == 133940, results
    assert results["fresh_wagon_checks"] == 48167, results
    assert results["split_checks"] == 48167, results
    results["status"] = "passed finite regression; not a Lean certificate"
    return results

if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
