# Track 7 — palette, changing edge type, and unrestricted order input
**15 November 2026. Draft source-level audit; no new kernel result.**

## What is already verified

The universal `q>2` induction for genuine **two-copy strong/linear
partite inputs** was verified at exact head `c4994bcd797e9eb720befb19542c86e760ca9484`:
full Lean Actions run #43652692100 and focused Track D #43652692120,
with five successful `#print axioms` checks. It is merged on main
as `6e5290f4632bf6fec5c791f1c4e88c0ec54df3a9`.
The separate one-physical-edge case is also merged (PR #1072).

These successes **do not** certify the unrestricted train Ramsey theorem.

## Quantifier order needed by cutoff two

The manuscript's shorter train uses:

* a NEW ordered coloured edge structure `X`, namely the EHN witness,
  not necessarily the original finite edge `A`;
* a NEW palette of functions from the edges of `X` into the original
  finite palette. Its cardinality is `r ^ |E(X)|`.

Thus the lower induction predicate must quantify over both the finite
**edge type** and all finite nonempty **palettes** before recursing.
`TrainRecursiveUniformAllColours` and
`TrainRecursiveUniformAllInputs` provide this strengthening of the
ALREADY CHECKED `q>2` partite step. They contain no new existence oracle.

The latest historical #1071 CI head `1c7eea4f` failed in
`UniformSelectedPartiteOrderAllColours.finPower` because Lean tried
to infer an arbitrary `Finite ?m` while the implicit target/base
carriers were still metavariables. The clean branch introduces those
carriers explicitly before specialising the order hypothesis.
This is a **proof candidate pending compilation**, not a passed repair.

## Why type/palette uniform PARTITE order is not RR_tail

The crucial issue is not a palette or universe error. The shorter
train `M_s` need not have a global fine part map indexed by vertices
of `X`.

Suppose original first wagons `F_p,F_q` meet in one vertex `v`.
Their copies `u_p(v),u_q(v)` are **distinct** in their disjoint union
`W`, hence `s(u_p(v)) != s(u_q(v))` for injective `s:W->X`.
The two canonical X-edge parameterisations of `M_s` send these
distinct X-coordinates to the same old vertex `v`. If there were a
global map `part: V(M_s)->V(X)` preserving both X-coordinate charts,
then it would have to satisfy simultaneously

```text
part(v) = s(u_p(v))  and  part(v) = s(u_q(v)).
```

This is impossible. The general abstract contradiction is recorded in
`no_global_X_part_of_colliding_canonical_edges`.

**This does NOT make the shorter train an invalid coloured-edge
structure.** The source `paper/04-coloured-edges.tex` expressly permits
a coloured edge structure `X` with several vertices in the *same
coarse unary predicate*. The two identified X-coordinates both inherit
the same original coarse predicate of `v`. It is the EXTRA requirement
of global fine X-partiteness that fails.

## A corrected nonpartite order predicate

`UniformSelectedUnrestrictedOrderAllInputs` quantifies over arbitrary
finite ordered trains `B` of a finite ordered edge type `A`, their
actual labelled train relation and girth/parameter certificates, and
all finite palettes. There is **no `B.IsPartiteOver A` premise**.

Its output uses an actual `OrderStage A B B {id}`:
a partite picture **over the whole target B** is legitimate, and does
not require an A-coordinate map on the INPUT B. The existing one-edge
proof in merged PR #1072 directly gives the complementary one-copy
specialisation `unrestrictedOrder_oneEdge_case`.

The corrected conditional operator is
`uniformSelectedUnrestrictedOperators`: its `largerCutoff` field
comes from the already verified universal partite `q>2` step, whereas
its `forestToOrder` field must produce an **unrestricted** order
witness. The `cutoffTwo` field consumes that unrestricted witness,
not the incorrect partite-order predicate. Neither field is proved
by introducing this record.

## Remaining substantive gates

1. Prove the real unrestricted same-vector
   `F_t -> RR_t` construction, including all selected-copy labels and
   system girth at every original cut (Track 4).
2. Prove cutoff-two filling (Track 5) using the **unrestricted** order
   predicate at the newly chosen edge type `X` and enlarged palette.
3. Construct the actual selected base `F_[2]` and discharge the outer
   coloured-edge transfer/height-one extraction (Tracks 1, 7, 8).
4. Keep the strong/linear two-copy assumption in `q>2` separate
   from the merged one-edge final-domain alternative.

## Verification

Only exact-head builds certify these new declarations. Run a pinned
Lean/mathlib full-project build and focused `scripts/check_track_d.sh`
with `#print axioms` for the new palette, all-input, obstruction, and
nonpartite interface declarations. The current agent container has no
Lean/lake/cache, so **this branch is uncompiled**; no source-only audit,
historical green run, or older manuscript validation mark substitutes
for that evidence.
