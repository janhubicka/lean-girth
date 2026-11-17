# Track 6 — current proof and validation map (17 November 2026)

This file supersedes the chronological draft inventory previously stored here.
Historical checks and unsuccessful variants are in the Git history and
[issue #1057](https://github.com/janhubicka/lean-girth/issues/1057).

## 1. Current branch scope

**Candidate branch:** `validation/6-double-count-candidate-20261113`.
**Status:** four genuinely new Lean proof modules, **18 new theorem declarations**,
all included in `CheckTrack6RefinementDoubleAxioms.lean`; **UNCOMPILED**.
No new `sorry`, `admit` or explicit axiom declarations; this is a static
source audit, not a certificate. Do not promote the stronger girth marks yet.

| Candidate file | Actual new target |
| --- | --- |
| `Girth/TrainRecursiveRefinementDoubleCount.lean` | `card_double_le_of_two_preimages`: an injection `Bool × usedLabel ↪ Fin n` yields `2 * card usedLabel ≤ n` |
| `Girth/TrainRecursiveRefinementDoubleStep.lean` | no used child label has a singleton occurrence; full one-step localization for cycles of length `≤2*g+1`, including physical `BergeCycle` |
| `Girth/TrainRecursiveRefinementDoubleGirth.lean` | repeated one-step descent inside a first wagon; local `>2g+1`, universal-first/height-one case, and global `>min(2g+1,h₁)` with an **actual retained first labelled-cut** hypothesis |
| `Girth/TrainRecursivePhysicalFineGirthDouble.lean` | conditional full physical A-support specializations from actual fine system certificates and first-cut information |

The doubled-descent tactic proof is **textually identical** to the older
mainline `g+1` descent after normalizing the numerical bound and
the name of the one-step lemma. The new geometric and arithmetic
content is concentrated in the first two files.

Two formerly proposed adapters have been **removed as redundant**:
`TrainRecursiveRefinementAllRetainedCuts` and
`TrainRecursiveRefinementCompleteCutVector`. Also removed the unused
`TrainRecursiveRefinementSelectedTransport` and
`TrainRecursiveRefinementSinglePartAcyclic` wrappers. Their needed
results are available from the checked mainline sources below.
No existing mainline theorems were altered.

## 2. What the checked mainline ALREADY proves

At **`lean-girth/main@cd76b3ba6d43b7095a72dd53de972b754b36389e`**,
[full Lean workflow #43950179891](https://github.com/janhubicka/lean-girth/actions/runs/43950179891)
**succeeded**. The workflow builds every `Girth/*.lean` module and
executes each `Check*.lean`, strictly allowing only `propext`,
`Classical.choice`, `Quot.sound`. The named theorems below have
actual matching `#print axioms` checks in that green run:

- `LabelledBergeCycle.child_not_injective_of_singleton_intersections`
  and `child_constant_of_singleton_intersections`: the existing
  one-part / `g+1` localization result.
- `FirstWagonRefinement.forget_train_eq`, retained parameter and
  quotient maps, `labelledGirthGT_at_retained`: exact coarse train,
  genuine wagon labels and original cutoff values.
- `activeGluingWitness_retainedFullSystem_all_tail` and
  `activeGluingWitness_retainedFull_exact`: preserve **full system
  girth**, not just labelled edge girth, at each actual retained cutoff.
- `ForestTailStage.trueActive_inducedAllLowerCutGirth`: the exact
  replicated lower cutoff vector `replicate (R.extraCuts+1) (q-1) ++ tail`.
- `ForestTailStage.coarsenedSelected_actualIndexedLocalInputBundle`:
  **injectivity of actual selected support pieces**, mixed forests,
  exact fine train restriction and parameters, and the
  **indexed selected-copy Ramsey arrow** from a genuine lower stage.
- `ForestTailStage.orderedTrueActiveSelected_indexedInputAndTwoCopies_of_nontrivial`:
  the ordered active nontrivial specialization.
- `ForestTailStage.refiningPictureStep_of_actualLowerSelectedStage`:
  from an actual lower selected `ForestTailStage` and `DesignatedArrow`,
  **plus the stated standing old-stage geometry** (A-linearity, the
  strong designated base family, two distinct target A-copies, a
  genuine nontrivial active fibre, a large partite base, part-preserving
  family, and current first-refinement readiness), derives output
  `hFull`, `hTail`, physical injectivity, parameters and indexed
  arrow, then constructs the real nontrivial `q>2` picture step
  and preserves readiness on unprocessed profiles.
- `untouchedActiveFirstWagonRefinement_of_finiteMixed` and
  `untouchedSubcarriers_labelledGirth_of_finiteMixed`: the fresh
  level construction with actual support-piece injectivity.
- `boundaryIncidenceGraph_isAcyclic_of_forest_part`: one-part
  restriction of a genuine finite gluing forest is acyclic.

**Important distinction:** the conditional nontrivial `q>2`
picture step is now already **kernel-checked** on main. The actual
lower selected `ForestTailStage` and `DesignatedArrow` remain
inputs and must be obtained by the **well-founded recursion
(Track 7)**. This stage-existence obligation must not be turned
into a current-rank oracle. The optional doubled-girth improvement
is not required for that recursion, which uses the checked `g+1`
consequence.

## 3. Manuscript alignment

The candidate English edits are on
`janhubicka/girth/revision/track6-refinement-proof-clarity-20261113`
(`paper/15-refinements.tex`, `paper/04-local-forests.tex`).
The one-step `2g+1` proof uses a finite bipartite graph of **literal
used child labels** and distinct connectors at label changes.
Every used label occurs at least twice; with `n≤2g+1`, at most
`g` distinct labels occur. If the child word were nonconstant,
the switching graph would have minimum degree two and contain a
labelled cycle of at most `g` labels, contrary to child-cut girth.
The first-wagon descent follows the old checked `g+1` proof.

For a nonempty tail, **do not** claim global `>2g+1` without
additional retained first-cut information: the sharp general
conclusion is `>min(2g+1,h₁)`. An actual 3-partite four-cycle
with `g=2,h₁=3` refutes the unconditional assertion.
Repeated nonadjacent labels and distinct labels with equal carriers
must stay distinct in the incidence analysis.

`lem:revisioninc` now cites the **existing, checked conditional
picture-step theorem** and records its actual lower-stage dependence.
The abstract ordinary-train statement and the optional doubled-girth
strengthening remain open as full Lean correspondences; the checked
reusable ingredients have `\\leanpartial` annotations. There has
been **no promotion** of the full lemma to verified status.

## 4. Diagnostics and next genuine gate

The locally mounted bounded checker
`/mnt/data/check_track6_min_degree_20261115.py` passed on
17 November: 142,416 canonical partitions of cyclic lengths 2–10;
switching-only incidence graphs; depth-two sharp
`2g+2` examples (`2≤g≤20`); retained-tail witnesses
(`2≤g≤16, g+1≤h₁≤2g`); equal-carrier label collisions;
and an acyclic physical path with cyclic grouped wagon carriers.
**This is finite regression evidence, not Lean verification.**
The mounted script has not been verified byte-identical to the
latest remote checker.

The local container has **no `lean`, `lake` or `elan`**,
and direct GitHub DNS does not resolve. Prior offline bundles expired.
No new paid CI was started. To certify the optional strengthened
proof at an exact branch head, use the repository's pinned Lean
v4.35.0-rc3 and all pinned Lake dependencies, then:

```sh
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleCount
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleStep
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleGirth
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursivePhysicalFineGirthDouble
LEAN_NUM_THREADS=1 lake env lean CheckTrack6RefinementDoubleAxioms.lean |
  tee CheckTrack6RefinementDoubleAxioms.log
python3 scripts/check_axioms.py CheckTrack6RefinementDoubleAxioms.log   CheckTrack6RefinementDoubleAxioms.lean
```

Only a successful exact-head build and strict transitive axiom check
can certify the 18 stronger statements. The already-checked `g+1`
recursion does not wait for them.
