# Track 6 — doubling candidate and exact validation gate

**Uncompiled. Do not promote any manuscript validation marker.** No paid Actions were requested.

Frozen manuscript baseline: `girth/main@8c9cfa6e`, source digest `45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
Working English proof: `girth/revision/track6-refinement-proof-clarity-20261113@22c27a89` (different source digest).
Lean branch base: `lean-girth/main@4d102cae`.

## Exact theorem interfaces

- `TrainRecursiveRefinementDoubleCount.lean`: `card_double_le_of_two_preimages` — pure finite injection, no geometric inputs.
- `TrainRecursiveRefinementDoubleStep.lean`: `child_has_second_occurrence_of_singleton_intersections` and `child_constant_of_singleton_intersections_twice` — requires transversality, singleton-part sibling intersections, complete labelled child girth >g.
- `TrainRecursiveRefinementDoubleGirth.lean`: `girthGT_firstWagon_twice`, `girthGT_of_first_universal_twice`, `girthGT_of_retainedFirstCut_twice`, `actualSupport_girthGT_of_retainedFirstCut_twice` — iterated local descent, universal empty-tail case, retained-cut cap `min (2*g+1) h`, actual A-support specialization.

## Local certification commands (NOT YET EXECUTED)

```bash
lake env lean Girth/TrainRecursiveRefinementDoubleCount.lean
lake env lean Girth/TrainRecursiveRefinementDoubleStep.lean
lake env lean Girth/TrainRecursiveRefinementDoubleGirth.lean
```

Each file prints endpoint axioms. Check output for `sorryAx`, unintended axioms, and elaborated assumptions. Do not treat presence of source-level proofs as kernel validation.

## End-to-end limits

Existing older `g+1` conditional adapter remains independent and sufficient for the recursion. The new doubling estimate must not replace the q-1 mixed-forest induction.
Missing from this candidate: actual fine selected witness, original-tail full-system bounds, selected Ramsey arrow and strong embeddings, and fresh-cut output-tail preservation. These require Track 3/4 and Track 7 integration.

Adversarial boundaries: classes may reappear nonadjacently; the local `2g+2` sharp example requires depth two; nonempty-tail global doubling is false for `g=2,h1=3` (four-cycle); parent-local child girth does not imply global retained first-cut girth.

Bounded Python diagnostic (not Lean): 142,416 set-partition words through length 10; all checks passed.

## 14 November continuation (new conditional endpoints)

- `TrainRecursiveRefinementDoubleGirth.lean` now treats the **bottom equality cut** separately with the existing noninjectivity lemma. Its displayed argument does not *use* the record's bottom child-girth field. The record still contains that field; hence this is **not** a theorem with a genuinely weakened input structure, and it must not be advertised as such.
- Added `FirstWagonRefinement.actualSupport_girthGT_of_first_universal_twice` for true A-support with an explicitly universal first wagon.
- Added `Girth/TrainRecursivePhysicalFineGirthDouble.lean`, with two conditional endpoints: `selectedPicture_actualSupport_girthGain_twice_of_fineSystemCuts` derives true physical A-support girth `> min(2*g+1,h)` from the same named fine bottom/positive system bounds, genuine parent parameters, and retained actual first full-system cutoff `h`; `selectedPicture_actualSupport_girthGain_twice_of_firstUniversal` gives the empty-tail `>2*g+1` under explicit first-universality. Neither constructs the selected lower witness or output stage.
- Extended the manuscript-branch finite test: besides all sharp `2g+2` examples for `2<=g<=20`, it now checks **every** smaller retained-tail cutoff `g+1 <= h <= 2g` for `2<=g<=16`, building an `h+1`-cycle of singleton first wagons with valid part assignments. All local Python tests passed.
- As of this audit, upstream `girth/main` has moved to `6e2048b7cbc6d16c27dfcdaf8e67924f5906f846` with unrelated changes; the manuscript branch has no overlapping changed paths but is intentionally not merged. `lean-girth/main` has moved to `b0b3c49a7d2b47150f146df588b5868be9d6cce3` with documentation and workflow changes.
- An offline local Lean installation using the *historically verified* 8 Nov GitHub Actions artifacts was investigated. The original nine artifacts are no longer listed on workflow run `42512209025` (expired); the container has no installed Lean, Lake, or mathlib and cannot resolve GitHub. **No Lean elaboration or axiom audit occurred**. No replacement Actions runs were triggered.
- Source-level inspection confirmed pinned Mathlib defines `finRotate : ∀ n, Equiv.Perm (Fin n)` and `Fintype.card_bool`, which are used by the candidate; this is API inspection, not a compilation result.

**Next exact-head gate:** compile `DoubleCount`, `DoubleStep`, `DoubleGirth`, `PhysicalFineGirthDouble` in order and run their printed axioms before changing any manuscript validation marker. Reuse all existing `g+1` certificates without waiting for the stronger estimate.

## 14 November evening: complete cut vector and independent geometry

The newest Track 6 additions are intentionally split between the new
doubling theorem and interfaces already supplied by the old formalization.

| Module | New endpoint | Contract and provenance |
|---|---|---|
| `TrainRecursiveRefinementDoubleStep.lean` | `BergeCycle.child_constant_of_singleton_intersections_twice` | Direct physical-cycle counterpart of the labelled (2g+1) one-step lemma. |
| `TrainRecursiveRefinementDoubleGirth.lean` | `FirstWagonRefinement.actualSupport_girthGT_firstWagon_twice` | Actual irreducible A-support, LOCAL first wagon; no retained global first-cut assumption. |
| `TrainRecursiveRefinementAllRetainedCuts.lean` | `allRetainedLabelledCutGirth`, `allRetainedLabelledCutGirth_mono` | Independent of doubling; aggregates existing exact quotient-index transfer at **every** old positive level. Requires actual old cut certificates. |
| `TrainRecursiveRefinementCompleteCutVector.lean` | `ForestTailStage.trueActive_sharedFineCutVector` | Combines the **existing** global inserted-cut theorem with each separately retained old positive cutoff. The head/tail pointwise comparisons are explicit arithmetic inputs; it does not assume a new global fine-girth conclusion. |
| `TrainRecursiveRefinementCompleteCutVector.lean` | `ForestTailStage.trueActive_inducedFineCutVector` | Transports the preceding whole vector from shared physical A-support to the true induced active relational A-support via the existing injective source map. |

### Existing formal components reused

- `TrainRecursiveParentChildCutGirth.lean`:
  `EdgeTrainLevels.labelledCutGirth_of_parent_and_children`,
  `FirstWagonRefinement.labelledCutGirth_inserted_of_retained`.
  The latter descends from a **global retained parent cut** and all
  actual parent-local child bounds; it is not a theorem that local
  child bounds alone give global girth.
- `TrainRecursiveTrueActiveRefinementCutGirth.lean`:
  `ForestTailStage.trueActive_sharedInsertedCutGirth` and
  `trueActive_inducedInsertedCutGirth`; the old stage supplies
  the global first retained cut.
- `TrainRecursiveTrueActiveRetainedTailCuts.lean`:
  `trueActive_sharedRetainedTailCutGirth` and
  `trueActive_inducedRetainedTailCutGirth`, retaining the
  stronger individual old tail entries, not just the head.
- `TrainRecursiveRefinementForget.lean` and
  `TrainRecursiveRefinementParameters.lean`: exact relation,
  wagon-class, parent, and parameter restoration.
- `TrainRecursiveCoarsenedSelectedRestriction.lean` and
  `TrainRecursiveCoarsenedSelectedFamilyArrow.lean`:
  indexed selected embeddings/arrow remain separate genuine
  lower-stage interfaces, not consequences of girth alone.

The main conditional real-fine-support double-girth wrapper remains
`selectedPicture_actualSupport_girthGain_twice_of_fineSystemCuts`.
Both versions of the new complete-cut-vector theorem require a
REAL `ForestTailStage` and a REAL `FirstWagonRefinement`;
neither theorem creates them.

**Exact-head check procedure after restoring the pinned toolchain and all dependencies:**

The new imports need compiled `.olean` objects first. Use Lake's named-module build targets (and limit Lean workers under low memory), then execute the checker:

```sh
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleCount
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleStep
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleGirth
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursivePhysicalFineGirthDouble
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementAllRetainedCuts
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementCompleteCutVector
LEAN_NUM_THREADS=1 lake env lean CheckTrack6RefinementDoubleAxioms.lean
```

Do not use an unpinned mathematical library or silently `lake update`.
The root `lakefile.toml` pins the partite-construction and successor-tree
dependencies and `lean-toolchain` pins Lean v4.35.0-rc3; respect their
transitive dependencies when restoring caches.

The central audit file now contains **22** source-level `#print axioms`
queries. These have **not been executed**; there is no kernel certificate
and the entire Track 6 remains open. The old (g+1) recursion path is
independent of doubling and must remain so.

### Adversarial finite diagnostics and source conflicts

The manuscript-branch checker now additionally verifies that two
distinct quotient-wagon labels with identical carriers form a genuine
labelled Berge 2-cycle and that deduplicating them invalidly removes
it. It also checks the ordinary acyclic four-edge path whose grouped
wagon cut forms a labelled Berge 3-cycle. The local suite passed;
these checks are bounded diagnostic evidence, not formal proofs.

Current `girth/main` has moved since the frozen 41-page baseline,
but none of `paper/04-local-forests.tex`,
`paper/15-refinements.tex`, or `Makefile` is modified by those
intervening commits. Do not overwrite concurrent updates to other
paper sections. The Track 6 manuscript changes remain on their own
branch; they have not been merged.

### Height-one empty-tail specialization and axiom inventory

The doubled-girth module now additionally provides
`FirstWagonRefinement.girthGT_heightOne_twice` and
`FirstWagonRefinement.actualSupport_girthGT_heightOne_twice`.
For a true height-one train, `T.top` itself proves that its first
positive relation is universal, so the empty-tail statement no longer
needs an independently supplied universality hypothesis. This is an
exactly stronger interface for the empty-tail branch, conditional only
on the original first-wagon refinement and edge transversality.

A fresh static source audit fetched **all six candidate modules** and
the central checker, counted **22 theorem declarations and 22 fully
qualified #print axioms requests**, and found no active source
`axiom`, `sorry` or `admit` declarations. This is **not** a Lean
elaboration/axiom certificate; all new statements are still candidates.

### 15 November: selected-map transport and exact static audit

New module `Girth/TrainRecursiveRefinementSelectedTransport.lean` proves
two **conditional** statements:

- `EdgeTrainLevels.forgetFirstCuts_map_rel_iff`: a specified edge map
  preserving **and reflecting** all fine train relations preserves
  and reflects every coarsened relation using the literal retained index.
- `EdgeTrainLevels.forgetFirstCuts_selected_rel_iff`: the **same**
  indexed family of injective physical-edge maps retains these
  equivalences, with no quotient of selected-copy labels or change
  in the underlying maps.

These discharge the *train-relation* component of the manuscript's
"same selected embeddings after forgetting" claim. They do **not**
create the lower selected family, prove its Ramsey arrow, or
construct its strong induced hypergraph embeddings. Those are
separate checked or conditional modules in Tracks 3/7.

The central `CheckTrack6RefinementDoubleAxioms.lean` now imports
**seven** candidate source modules and requests **24** fully qualified
axiom outputs. A namespace-aware static scan of the preceding
22 declarations found exact one-to-one name correspondence and
no active proof placeholders. Repeat that scan for the two added
transport declarations; neither a static scan nor source inspection
is a kernel build. **All new Track 6 declarations remain unverified.**

The complete narrow build sequence now includes:

```sh
LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementSelectedTransport
LEAN_NUM_THREADS=1 lake env lean CheckTrack6RefinementDoubleAxioms.lean
```

The selected transport build should be run after the other six
new candidate modules; it is independent of their doubled-girth
proofs. The root axiom checker requires all imports' `.olean`
objects. No online or expensive CI run has been initiated.

### 15 November adversarial simplification of the English argument

The one-step observation in the manuscript branch now has a shorter
**minimum-degree incidence-graph proof**. If the child word is not
constant, every used child label has at least two edge occurrences,
hence at most `floor(n/2) <= g` labels for `n <= 2g+1`.

Use the bipartite graph whose nodes are these **literal** child labels
and the actual distinct connectors at switches between adjacent
labels. Every switch connector meets two different child carriers,
so its graph degree is at least two. Every occurring child has a
maximal cyclic run with **two distinct switching connectors**, so
every child node also has degree at least two. The graph is finite,
nonempty and has minimum degree at least two, hence a simple cycle.
That cycle is a labelled Berge cycle using at most `g` child
labels, contradicting the complete labelled child-cut girth `>g`.
No compressed walk or no-immediate-reversal explanation is needed
in the English manuscript. The Lean candidate can reuse the
previously checked compressed-incidence machinery; exact exposition
need not coincide with a formal proof's implementation details.

A new Python diagnostic constructs this **switching-only graph**
for all 383 canonical nonconstant/no-singleton-run words among the
142,416 set partitions of cyclic lengths 2 through 10; it checks
degree >=2 on BOTH node sorts and verifies a cycle in every case.
The full checker also repeats the explicit 3-uniform sharp and global
counterexamples and literal labelled-wagon regressions. The full
local Python suite passed on 15 November.

The current same-selected-edge-map transport module and the central
strict axiom checker are on the Lean branch, still **uncompiled**;
the source-level inventory is 24 declarations and 24 distinct
fully qualified `#print axioms` queries. No manuscript
validation marker has been promoted, and mainline was not modified.
