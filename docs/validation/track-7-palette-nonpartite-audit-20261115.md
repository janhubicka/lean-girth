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

Historical #1071 attempted an additional *partite-order* palette
specialisation and failed to elaborate its implicit target/base
`Finite` instances. That endpoint is **not used** by the correct
unrestricted cutoff-two recursion. The clean branch therefore removes
the partite-order wrappers and their auxiliary `Operators` records
entirely, retaining just
`UniformSelectedPartiteForestAllColours_largerCutoff` and
`UniformSelectedPartiteForestAllInputs_largerCutoff`.
The necessary unrestricted-order palette specialisations are stated
separately in `TrainRecursiveUnrestrictedOrderInterface`.

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

**Second, independent obstruction: the base cannot be fixed to B
with the singleton identity family except in the one-copy case.**
If B contains embeddings a₁,a₂:A→B with a₁(u)≠a₂(u), colour each A-copy
e in any B-partite output picture by its projected B-part at u (or use
the Boolean test `part(e(u))=a₁(u)`). Every designated B-copy whose
base embedding is the identity then has different colours on
its a₁ and a₂ subcopies. No identity-base `DesignatedArrow` can exist.
The new `no_identityBase_designatedArrow_of_distinct_A_values`
formalizes this obstruction independently of girth assumptions.

Accordingly the *repaired* output is
`UnrestrictedSelectedOrderWitness A B t targetTrain allowed κ`:
it existentially chooses a finite, potentially larger Ramsey base D,
an actual family of B-embeddings into D, appropriate permitted sets on
D whose pullback inside every prescribed B-copy is contained in the
original permitted set, and an actual `OrderStage A B D family` with
`DesignatedArrow`. The INPUT B need not be A-partite, and the selected
B-copies are not forced to project to the identity in B.

The verified one-copy theorem #1072 still produces the canonical
identity-base `OrderStage` in that genuinely special case. The new
`unrestrictedOrder_oneEdge_case_general` injects it into the stronger
existential-base output. None of this constructs the missing general
unrestricted forest-to-order transfer.

**Coarse-predicate parameter transport:** the unrestricted order
predicate records allowed sets as subsets of the vertices of B.
For an original coarse unary predicate map `colour_B : V(B) → I`
and a permitted index set `S ⊆ I`, choose the B-vertex set
`colour_B^{-1}(S)`. If the resulting picture has part map
`part : V(H) → V(B)`, then its permitted vertices are exactly
`part^{-1}(colour_B^{-1}(S)) =
(colour_B ∘ part)^{-1}(S)`. Thus a picture partite over the WHOLE
target B can still preserve the original coarse predicate
intersection restrictions after forgetting its auxiliary B-parts.
The actual cutoff-two application must verify that its shorter
target carries these prescribed allowed sets at every cut.

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

## 15 November adversarial correction: nontrivial target base

The original draft #1073 unrestricted statement was **false**: it
quantified over arbitrary B but fixed its base to B and its family to
{identity}. A nontrivial B has two A-embeddings with different vertex
images at some u; the induced colour by the B-part at u is not
constant on any identity-projected designated copy. This is independent
of the earlier obstruction involving collisions between X-coordinate
charts in the cutoff-two construction.

The corrected output permits an existential finite base D and a family
of B→D embeddings, with allowed-set pullback compatibility, and produces
an actual selected OrderStage over D. The one-copy identity-base theorem
remains a valid special case. Exact-head Lean and axiom checks of these
new declarations are required; static audit alone is not certification.

## Critical-path cleanup after the nonpartite RR repair

The fixed-input PartiteOrder operators were a historical exploratory
path, not an input to the correct `Operators` record. They were
removed from the new branch along with their failing palette
specialisation and six redundant axiom probes. The only new FOREST
claims needed here are uniformity over finite colour types and finite
ordered edge types for the already checked q>2 transition. The unique
unrestricted `forestToOrder` field must return the existential-base
`UnrestrictedSelectedOrderWitness`; it is still an explicit unproved
hypothesis. Consequently no mathematical strength is lost by deleting
the partite-order wrappers.

The unrestricted-order interface also exposes the literal colour-word
palette `Fin n → Fin r`. This avoids a separate numeric coding
`Fin (r^n)` in the actual cutoff-two application: after choosing
an enumeration of the finite edges of X, the colour of a shorter-train
edge is directly a function recording all original edge colours.

All of these changes are proof-candidate/source-only work on this PR.
Neither the unrestricted order assertion nor cutoff-two realization has
been Lean-certified or promoted in the manuscript.
