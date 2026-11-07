#!/usr/bin/env python3
"""Finite adversarial regression for Path A's two-owner-cut singleton transfer.

Theoretical input: owner changes at a source position t exactly when
owner[t] != owner[(t+1)%n]. The canonical cut indexing is increasing.
For n>=3 and exactly 2 changes, forward adjacency of consecutive
cut indices forces the run ending at the later cut to be a singleton;
all other source positions have the other cut's geometric owner.
If the two cuts are adjacent, exactly one forward orientation works.

This is a finite sanity check, not a substitute for Lean validation.
"""

from itertools import product


def check(max_n: int = 8, alphabet: int = 3) -> None:
    counts = [0, 0]
    orientations = [0, 0]
    example_reverse = None
    for n in range(3, max_n + 1):
        for word in product(range(alphabet), repeat=n):
            cuts = [
                t for t in range(n)
                if word[t] != word[(t + 1) % n]
            ]
            if len(cuts) != 2:
                continue
            counts[0] += 1
            forward = []
            for j in range(2):
                p = cuts[j]
                q = cuts[(j - 1) % 2]
                fwd = p == (q + 1) % n
                rev = q == (p + 1) % n
                assert not (fwd and rev), (n, word, cuts, j)
                if fwd:
                    assert all(word[t] == word[q]
                               for t in range(n) if t != p), (
                        n, word, cuts, j
                    )
                    forward.append(j)
            if forward:
                counts[1] += 1
                assert len(forward) == 1, (n, word, cuts, forward)
                orientations[forward[0]] += 1
                if example_reverse is None and forward == [0]:
                    example_reverse = (n, word, cuts)

    assert counts[0] > 0 and counts[1] > 0
    assert all(orientations), orientations
    assert example_reverse is not None
    print(
        f"PASS: {counts[0]} exact-two-cut owner words, "
        f"{counts[1]} adjacent-cut words, "
        f"forward orientation counts={orientations}; "
        f"wrap example={example_reverse}"
    )


if __name__ == "__main__":
    check()
