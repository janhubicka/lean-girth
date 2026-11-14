# Numbered Track 7: universal lower-rank assembly (14 November 2026)

**Status:** source-level proof candidate in draft PR #1070, not Lean-certified.
This branch starts from **merged and exact-head kernel-checked** PR #1066
(`lean-girth/main@d1f79d1758b8ccad9a23540cd0e33f2ad756fd50`).
The successful CI on #1066 does **not** cover these new universal statements.

## Exact induction assertion

`UniformSelectedPartiteForest A₀ t κ` quantifies over *all* finite
ordered A-partite target systems and large bases with a part-preserving
selected target family, and retains:

- target physical A-support **nonemptiness**, full vertex coverage,
  ordinary girth at `t.headD 0` and all positive **labelled** target cuts;
- adjacent sibling allowed-part parameters at every fine train coordinate;
- genuine A-linearity of the target and base, A-partiteness of both,
  and A-strongness of the **whole prescribed base family**;
- a real partite family arrow with the prescribed *embedding* family,
  not merely an unindexed projection;
- **two physically different A-copies in the target.** One-copy targets
  need a separate branch and are not silently included.

Its conclusion is a literal selected `ForestTailStage` and
`DesignatedArrow stage κ`, not a mere ordinary colouring arrow.

`UniformSelectedPartiteOrder` has the same exact input domain and outputs
an actual `OrderStage` (all-cut full system girth), still with a
`DesignatedArrow` on its parent forest stage.

## q>2 field, without circularity

The `UniformSelectedPartiteForest.largerCutoff` candidate uses
`hAllLower d` only for **positive** depth `d` and at vector

```text
old:   [q] ++ tail
lower: replicate (R.extraCuts + 1) (q - 1) ++ tail
```

The old readiness invariant gives `R : FirstWagonRefinement` for each
nontrivial processed profile. The rank decrease is the already checked
`trainCutoffReplacement_wfRankDecrease` and holds at **every** positive
depth, including `R.extraCuts = 0`.

`TrainRecursiveUniformLowerHJBridge` obtains the large A-partite
Hales–Jewett base and A-strong line family *from the old true active source*
and the finite colour type. Source A-linearity/coverage, target two-copy
nontriviality, ordinary q−1 support girth, fine adjacent parameters, and
all lower-vector positive girth bounds are explicitly derived. The exact
train-height equality is

```text
(replicate (r+1) (q-1) ++ tail).length
    = ([q] ++ tail).length + r
```

with no quotienting physical labels or identifying selected indexes.
The universal **strictly lower-rank** hypothesis is then applied to this
actual HJ base, producing a genuine selected lower stage and its arrow.

`TrainRecursiveUniformLowerPictureStep` uses that stage and the
*already verified* `refiningPictureStep_of_actualLowerSelectedStage`
from PR #1066. The finite pass
`constructFromPartiteTargetCuts_of_freshNontrivialRefiningSteps`
handles absent/trivial *processed profiles* and assembles the q>2
universal selected forest assertion. This is not the same as the
separate one-copy *target* case.

## Remaining mathematical gates, still NOT proved here

1. `UniformSelectedPartiteForest A₀ [2] κ`: genuine selected base-two
   theorem in the stated nontrivial/strong-family input domain.
2. `UniformSelectedPartiteForest A₀ t κ → UniformSelectedPartiteOrder A₀ t κ`
   for the **same** vector, without a new rank-decreasing call.
3. `UniformSelectedPartiteOrder A₀ tail κ →`
   `UniformSelectedPartiteForest A₀ (2 :: tail) κ` for admissible nonempty
   tails: actual cutoff-two selected filling / restoration.
4. Extend the final theorem beyond the nontrivial two-copy input domain,
   using the separate one-copy/edge-only cases rather than assuming
   `hTargetTwo` for every target.

`uniformSelectedPartiteOperators` packages these **three explicit**
operator premises, and fills only `largerCutoff` with the constructed
q>2 theorem. The conditional rank assembly has no admitted proof.

## Verification

The five new Lean modules and checker have static delimiter/namespace
and no-sorry source checks only. **They have NOT been elaborated by Lean.**
Exact-head requirements before merge are:

```bash
bash scripts/check_track7_rank_local.sh
```

and the full project Lean build, full theorem/axiom audit and finite
boundary regressions. The checker tests the lower HJ instance, the
universal picture step, q>2 finite-pass closure, the Operators constructor
and the conditional final rank theorem. No manuscript green mark should
be added until the relevant *exact* theorem and its hypotheses have been
checked by the Lean kernel and independently audited.
