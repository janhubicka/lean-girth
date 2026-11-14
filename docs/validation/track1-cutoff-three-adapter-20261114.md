# Numbered Track 1 — exact reuse plan for cutoff three (14 Nov 2026)

**Status:** interface audit + uncompiled auxiliary Lean source, **not** a
new Lean/kernel certificate. Manuscript source: the draft
[girth #452](https://github.com/janhubicka/girth/pull/452).
Issue: [lean-girth #1052](https://github.com/janhubicka/lean-girth/issues/1052).

## Reuse, do not duplicate the full picture proof

The English manuscript now has a direct elementary 3-member argument:
`lem:threeboundaries` and `lem:threepicture`, preceding
`prop:forestthree`. The bespoke uncompiled Fin-3 join-tree module was
removed as redundant. The shorter `Girth/Track1CutoffThreeReuse.lean`
instantiates the existing generic, previously checked
`selectedForest_of_distinctOwners_girthOnly` at cutoff three.
This handles the all-distinct case but **not** the actual picture step.

For the paper-to-Lean end result, prefer the existing **conditional**
`Girth/ForestActualDesignatedTrueActiveIncrement.lean` theorem
`actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull`.
Its hypotheses are the precise interface for a genuine current picture,
without declaring arbitrary ownership or pruning ambient edges.
Specialize the theorem at `m = 3`, so `m - 1 = 2`.
It already reuses:
- `ForestActualDesignatedDirectIncrement` and
  `ForestFactoredCanonicalIncrement`;
- `ForestActualSmallGluingCarrier`,
  `ForestStandardSupportFactor` and actual attachment overlaps.

### Remaining arguments for the specialization

| Existing premise | Source/result to provide | Risk |
|---|---|---|
| `hOldForest` at `m=3` | induction invariant on the **whole** old picture, including all ambient A-edges | preserve actual edge carrier and labels |
| `hPrevious` at `m-1=2` | selected strong, controlled `A`-linear target images + every core A-edge: the mixed LF2 theorem in `TrainRecursiveBaseRamsey.lean` | **all ambient** core edges, not only selected edges |
| `hCoreGirth` at 3 | new triangle-free restricted functional EHN witness | central *new* missing Ramsey endpoint |
| `hAmbientGirth` at 2 | attached-picture `A`-linearity from `ActiveCarrierStrong.lean` / `ActivePicture.lean` plus `LinearityGirthTwo.lean` | do not assume the desired global girth >3 |
| `hSourceNonempty,hSourceCover` | active system with >=2 edges and local witness selected positive-edge coverage | isolated vertices should be removed only from the *local target* before construction |
| `hActiveRange,hFactor` | true-active carrier and exact attachment factorization | use the actual source and gluing maps |
| `hRegularAmbient,hCoreAmbient` | all old/central A-support edges actually occur in the new picture | no edge pruning during the induction |
| `hBaseStrong,hTestA,hTestB` | base-selected B images strong, and old mixed tests include all A and designated B pieces | never replace actual B by a reduced gluing label |
| `hSelectedInjective,hSelectedCard,hSelected` | a genuinely indexed set of <=3 **distinct physical** selected pieces, of actual new A-edge or transported B type | duplicate edge `e^+` must not be counted twice |

The resulting conditional `ForestOfCopies selected` does not by itself
give a local Ramsey witness. The remaining construction must deliver:
ordered indexed selected local target embeddings, the EHN Ramsey arrow,
fusion and final part coarsening, covering and private restoration of
isolated target vertices.

## Closure/Ramsey language

Use the existing `Girth/FunctionalEHNClass.lean` canonical `c_A`
class, `Girth/TargetClosure.lean`, and
`Girth/ALinearRamsey.lean`.
The shorter coloured-edge proof adds one **arbitrary** partial unary
function `d` of fixed positive range cardinality `|E|`, not the
old variable-size singleton owner. Since it is unconstrained in the
class, the intended proof is a forgetful-language adapter to the
checked `ElementaryCAClass_freeAmalgamationClass`. The
`A`-girth>3 subclass still needs a new free-amalgamation proof.
Keep the fresh EHN order and select only its full ordered target images.

## Concrete counterexample to weakenings

A core with a *single* 3-edge `{a,b,c}` has no Berge cycle.
Three pieces with respective intersections
`{a,b}, {b,c}, {a,c}` with this core have pairwise singleton
overlaps in a triangle. They have no 3-member join tree.
Thus "boundary is contained in an edge" does **not** replace
"boundary is the whole edge and is an edge of the piece".

Also the general separator replacement argument fails if `e^+`
already equals one of the selected members: the old family then
has only two physical members. The corrected manuscript handles
this with a direct 3-member path centred at `e^+`.

## Evidence and next checks

- Local finite tests: 74,230 narrow distinct-boundary configurations,
  13,200 repeated-picture edge-boundary cases (5,060 with `e^+`
  already selected); zero failures at their stated finite scopes.
- Independent negative tests catch a triangle core and the
  proper-subedge failure over an acyclic single-edge core.
- The retained `Track1CutoffThreeReuse.lean` is uncompiled and its
  elaboration and axioms remain unverified. `CheckTrack1.lean` is the
  focused check entrypoint; it has not been executed.
- The existing conditional picture theorem on `main` is reusable as
  a theorem declaration, but its required arguments have NOT been
  discharged for the new local witness.
- No automatic PR merge, validation-marker promotion, full paper
  compile or paid GitHub Actions requested.
