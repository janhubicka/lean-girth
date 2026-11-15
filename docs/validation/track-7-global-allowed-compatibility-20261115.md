# Track 7: global parameter compatibility in the unrestricted order witness

**15 November 2026 · independent source audit · no kernel check.**

The existential-base unrestricted order predicate in draft #1073 has
two good features absent from its earlier form: the output base D may be
larger than the input target B, and the input train B need not have a fine
A-partition. These are necessary for cutoff-two filling.

There is a further distinction between local *B-copy* compatibility and
global *ambient output* compatibility.

## Verified mathematical issue (elementary set theory)

The current proposed output data include the pullback requirement

    ∀ b ∈ family, ∀ ν, b ⁻¹' allowedD[ν] ⊆ allowedB[ν].

By itself it controls only **points of D lying in the images of the
prescribed B-copies**. It imposes no restriction on `allowedD[ν]` at
points outside those images. Such points may still be used by ambient
A-edges of the output stage and hence by actual wagon intersections.

For example take `B=Unit`, `D=Bool`, one B-map sending the unique
point to `false`, `allowedB=∅` and `allowedD={true}`.
The prescribed pullback requirement is true, while the nonempty
allowed D-point is outside the prescribed image. So per-family
pullbacks **do not imply** global coarse parameter bounds.

A sufficient additional condition is permitted-point base coverage:

    ∀ ν y, y ∈ allowedD[ν] →
       ∃ b ∈ family, ∃ x : B, b(x) = y.

Then the pullback property implies

    ∀ ν y, y ∈ allowedD[ν] →
       ∃ b ∈ family, ∃ x ∈ allowedB[ν], b(x) = y.

If the prescribed B-embeddings preserve the original coarse predicates,
and `allowedB[ν]` consists of permitted coarse-predicate vertices,
then **every** point of `allowedD[ν]` has a permitted coarse
predicate. Pulling this back through the new D-partite witness's
`part : Vertex → D` gives the original ambient intersection bound.

This is formally distinct from the previously detected X-coordinate
collision: the latter prohibits a *global fine X-part map* on the
shorter train; the present issue is about a **too-weak allowed-set
condition on a larger Ramsey base**.

## A simpler alternative: choose canonical coarse-permitted parts

In the manuscript's coloured-edge setting, the permitted vertices at
each cut are **unions of unary colour classes**, not arbitrary sets of
individual B-vertex coordinates. Suppose
`predB : V(B) → I` and `predD : V(D) → I` are the genuine coarse colour
maps and every prescribed embedding b:B→D preserves these maps.

For the original permitted predicate-index set `P[ν] ⊆ I`, CHOOSE

    allowedD[ν] = predD^{-1}(P[ν]).

This choice immediately gives **global** coarse compatibility for
every D-point, including those outside all selected B-copies. Moreover,

    b^{-1}(allowedD[ν]) = predB^{-1}(P[ν]).

Thus it satisfies the selected family pullback requirement whenever
`allowedB[ν]` contains the original permitted B-colour classes
(and with equality when `allowedB[ν]=predB^{-1}(P[ν])`).

In this canonical choice, **no permitted-point selected-family
coverage is needed**. This is potentially the preferable method for
the genuine coarse-coloured Ramsey output. However it is only useful
if the actual construction of the selected `OrderStage` permits
choosing its allowedD parameters in this canonical form. That existence
step has NOT been proved here. For a stage whose allowedD was already
fixed arbitrarily, the original coverage argument remains one possible
sufficient condition.

There is also a weaker intermediate alternative to covering all
allowed D-points: it suffices to cover the **actual output contact
vertices** at each train cut. The lemma
`usedContact_coarsePredicate_of_localPullback` formalizes precisely
this restricted obligation. It may be easier to establish from the
actual glued geometry than full selected-family coverage of D.

## Actual unary colours versus auxiliary part coordinates

The definition of `Partite.System L P V` in the pinned
`partite-construction/PartiteConstruction/Partite/Basic.lean`
has a part map `V→P` and a **transversality** condition on relation
tuples. It does NOT, merely by the definition of partiteness, impose
that the unary colour of an output vertex y equals the coarse
colour of its part `part(y)`.

Thus the canonical allowedD construction controls the **composed**
predicate `predD ∘ part` automatically, but transferring to the
**actual output unary predicate** `predOut` needs an additional
compatibility certificate

    ∀ y, predOut(y) = predD(part(y))

(or the same equation only for actual contact vertices at the
relevant cuts). In an initial labelled picture this may follow from
its component construction and colour-preserving embeddings; the
recursive attachment must preserve that invariant. It is NOT a
consequence of an arbitrary System's transversal field alone.

The conditional new statements
`adjacentParameters_of_canonicalCoarseAllowed_and_colourCompatibility`
and `usedContact_originalPredicate_of_colourCompatibility`
make this final step explicit. Neither constructs the needed colour
compatibility for the real attached picture.

## Lean interfaces

`Girth/TrainRecursiveGlobalAllowedCompatibility.lean` contains:

- `allowedBase_covered_of_familyPullbacks`: permitted D-base
  coverage + the existing local pullbacks → globally permitted image
- `allowedBase_coarsePredicate_of_coverage`: compatibility of
  unary coarse predicates → every allowed D-base vertex has an
  originally permitted coarse predicate
- `allowedVertices_coarsePredicate_of_globalBaseBound`: pull back the
  resulting bound through an arbitrary picture's part map
- `usedContact_coarsePredicate_of_localPullback`: only the genuine output
  contact vertices need coverage, provided their D-parts are allowed
- `adjacentParameters_of_canonicalCoarseAllowed_and_colourCompatibility`
  and `usedContact_originalPredicate_of_colourCompatibility`: explicitly
  require the actual output unary-colour map to agree with the colour
  of its base part, globally or on actual contacts
- `adjacentParameters_of_canonicalCoarseAllowed`: the genuine
  `EdgeTrainLevels.AdjacentParameters` predicate transfers unchanged
  from canonical D-parts to the composed original coarse predicate map
- `canonicalCoarseAllowed_pullback`,
  `canonicalCoarseAllowed_familyPullback`, and
  `canonicalCoarseAllowed_output`: choosing the permitted D-parts by
  original coarse unary colour immediately controls all D-points and
  restricts correctly to each selected B-image, without any coverage
- `localPullback_does_not_imply_globalCover`: the finite
  Unit→Bool counterexample above

These lemmas are **conditional preparation**, not an existence theorem
for a selected order stage. The preferred option is to choose canonical
coarse-predicate allowedD in the actual Ramsey construction. If that
choice is unavailable, one may prove coverage of allowed D-points or
only of the genuine output contacts; neither is proved here.

## Current validation boundary

This PR does NOT change the unrestricted predicate in live draft #1073,
its compiler errors, or any manuscript validation mark. Before
promoting an unrestricted order theorem, either **construct the stage**
with canonical coarse-predicate allowedD, or ensure the selected
family covers every permitted base point / genuine used contact vertex,
or prove another direct global coarse-predicate compatibility. Verify
the output's ambient wagon parameters, not merely those internal
to selected designated copies.

The new modules contain eleven exact axiom probes, with no `sorry`/`admit`/new axiom. They have
NOT yet passed an exact-head Lean compile or `#print axioms` check.
