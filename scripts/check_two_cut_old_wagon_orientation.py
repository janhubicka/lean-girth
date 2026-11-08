#!/usr/bin/env python3
"""Exhaustive finite sanity check of Path A's old-wagon two-cut orientation.

Source owner cuts are positions k with owner[k] != owner[(k+1)%n].
For exactly two cuts and an UNCUT wagon connector position t
whose predecessor and successor are both cuts, the canonical
increasing cut enumeration must identify cut j = succ(t) and
cut pred(j) = pred(t). All source positions outside t, succ(t)
must carry the owner at pred(t).

This regression checks every 3-letter owner word of length 3..9,
including wrap. It is not a substitute for Lean or the paper proof.
"""

from itertools import product


def verify(max_n: int = 9, alphabet: int = 3) -> None:
    two_cut_words = 0
    old_wagon_cases = 0
    cyclic_wrap_cases = 0
    for n in range(3, max_n + 1):
        for owner in product(range(alphabet), repeat=n):
            cuts = [k for k in range(n)
                    if owner[k] != owner[(k + 1) % n]]
            if len(cuts) != 2:
                continue
            two_cut_words += 1
            for t in range(n):
                a = (t - 1) % n
                b = (t + 1) % n
                if t in cuts or a not in cuts or b not in cuts:
                    continue
                old_wagon_cases += 1
                j = cuts.index(b)
                pred_j = cuts[(j - 1) % 2]
                assert pred_j == a, (n, owner, cuts, t, j)
                assert all(owner[x] == owner[a]
                           for x in range(n) if x not in (t, b)), (
                               n, owner, cuts, t)
                if b < a:
                    cyclic_wrap_cases += 1

    assert two_cut_words > 0
    assert old_wagon_cases > 0
    assert cyclic_wrap_cases > 0
    print("PASS: checked", two_cut_words, "two-cut owner words,",
          old_wagon_cases, "old-wagon two-step configurations,",
          cyclic_wrap_cases, "wrap orientations")


if __name__ == "__main__":
    verify()
