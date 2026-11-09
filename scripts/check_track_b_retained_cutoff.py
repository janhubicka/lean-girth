#!/usr/bin/env python3
"""Exhaustive small arithmetic regressions for the true Track B cutoff shift.

This is independent finite evidence, NOT Lean kernel validation.
The original old positive index j (1 <= j < |q::tail|) becomes the
actual lower positive index j+r in the vector
replicate (r+1) (q-1) ++ tail. The full old cutoff must be retained.
Also test the lower attachment's q-1/q positive interior budget.
"""
from itertools import product

vectors = retained = 0
for q in range(8):
    for r in range(6):
        for tail_len in range(5):
            for tail in product(range(8), repeat=tail_len):
                old = (q, *tail)
                fine = (max(0, q - 1),) * (r + 1) + tail
                assert len(fine) == len(old) + r
                for j in range(1, len(old)):
                    assert 0 < j + r < len(fine)
                    assert fine[j + r] == old[j]
                    retained += 1
                if all(a <= b for a, b in zip(old, old[1:])):
                    for nu in range(1, len(fine)):
                        required = max(0, q - 1) if nu <= r else q
                        assert required <= fine[nu]
                vectors += 1

assert vectors == 224688
assert retained == 866688
print(f"Track B retained-cut regression: {vectors} vectors, "
      f"{retained} exact positive old-cut identities passed")
