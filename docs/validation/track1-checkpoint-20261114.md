# Numbered Track 1 — checkpoint after adversarial simplification (14 November 2026)

**Manuscript main:** [girth@c66172b7](https://github.com/janhubicka/girth/commit/c66172b7f1283fdb378dd69de432876b1d6eb679).
The revised manuscript has been merged; TeX compilation remains manual.
**Lean working branch:** `validation/1-three-boundary-kernel-20261114`,
**not merged**, new modules uncompiled.

## Statement-by-statement audit

| Manuscript item | Existing checked library | What is new / still open |
|---|---|---|
| `lem:closedamalgam` | `ElementaryClosureAmalgam.aLinear_of_freeAmalgam`, strong-side lemmas | `Track1StrongOverlapGirthThree`, `Track1FreeAmalgamSupport`, `Track1StrongAmalgamGirthThree`: direct girth>3 closure; source candidate only |
| `obs:functionalinput` | `FunctionalEHNClass.ElementaryCAClass_freeAmalgamationClass` | `Track1TriangleFreeEHNClass` adds the restricted class and positive girth; source candidate only |
| `lem:basedclosure` | `TargetClosure.targetClosed_classify_nonempty`; `ClosureEmbeddingGeometry` | **No new target-closure language needed.** Optional canonical `c_M` and arbitrary `d` both removed from the preferred manuscript proof |
| `thm:AlinearRamsey` | `ALinearRamsey.closedTargetRamseyFamily_of_monotone_embeddings`; full closure embedding properties | `Track1TriangleFreeSelectedFamily`: same ordered EHN construction in the girth>3 class with explicit fresh-order-preserving selected family; source candidate only |
| `lem:unrestricted` | `TrainColouredEdgeOwnerSplit`, `SelectedLift`, `SelectedStrong`, `WholeEdgeIntersection`, `InducedUniformLift`, `ProjectionOrder`, `ExactColourTransfer` | `OwnerSplitGirth`, `OwnerSplitCoverage`, `OwnerSplitOrderArrow`, `OwnerSelectedFromEmbedding`, and `Track1SelectedOldStrong` (derive owner-split hOldStrong from actual A-strong selected B copy), plus final selected-family restriction/arrow; source candidates and final packaging pending |
| `lem:threeboundaries` | `ForestDistinctOwnersGirthOnly.selectedForest_of_distinctOwners_girthOnly` | Specialization `Track1CutoffThreeReuse` only; the redundant bespoke three-node proof has been **deleted** |
| `lem:threepicture` | `ForestActualDesignatedTrueActiveIncrement.actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull`; `TrainRecursiveBaseRamsey.mixedForestThrough_two_of_strong_controlledFamily`; `ForestActualRecursiveSupport.actualRecursiveMixedLocalForest` | `Track1SelectedMixedLF2` composes the two checked LF2 bridges; still requires distinct selected support representatives and true-active attachment data. The actual picture endpoint remains conditional |
| `prop:forestthree` | Existing partite geometry/fusion component lemmas | Finish selected local Ramsey witness, full backward fusion, order coarsening and isolated target vertices |

## Build readiness and exact validation gate

- `CheckTrack1.lean` imports **all** surviving candidate modules through
  seven roots and prints eighteen key theorem axiom sets. The new files are not
  imported by the repository's default `Girth.lean`: a normal
  `lake build Girth` does **not** validate them.
- `scripts/check_track1.sh` first builds those seven dependency roots
  with `LEAN_NUM_THREADS=1`, and *then* elaborates
  `CheckTrack1.lean` and rejects any printed `sorryAx`.
  A syntax-only shell check of the script passed.
- The current container has **no installed Lean/Lake**, no matching
  dependency checkout, no direct GitHub DNS. The old offline transfer
  artifact listing for run `42512209025` is empty (expired), so
  a local exact-head build was not possible in this session.
  **Do not treat the presence of `#print axioms` as its execution.**
- Source-only import audit: all 12 candidate files before pruning had
  resolved local `Girth.*` imports; after pruning, remaining candidates
  use only existing local imports and no literal `sorry`/`admit`
  declarations. Lean elaboration is still unknown.

On a machine with the matching dependencies already installed:

```bash
git switch validation/1-three-boundary-kernel-20261114
bash scripts/check_track1.sh
```

The printed Git HEAD and precise Lean compiler version must be recorded.
For any failed theorem, fix the earliest source error, rebuild the
same focused roots and inspect the actual checker output. Do not
promote manuscript validation marks before successful exact-head
compilation, audit of the printed axioms, and proof of the remaining
full selected-witness and fusion endpoints.

## Independent finite regression reruns

The locally executed distinct-source `A`-strong free-amalgamation
script reproduced all **408,749** cases with zero counterexamples and
byte-for-byte equal parsed JSON results. A second local rerun of the
owner-splitting test reproduced **285,200** exhaustive one/two-copy
cases plus **24,349** seeded three-copy cases, also with zero failures.
The separate small three-boundary report records **74,230** cases.
These are bounded support diagnostics, **not** EHN or Lean proofs.

## Adversarial corrections made in this continuation

- Removed duplicate uncompiled `ThreeBoundaryKernel` code that
  depended on unsupported bespoke star-graph helper names;
  reused the established generic forest theorem instead.
- Removed obsolete uncompiled unary-owner `d` bridge and the duplicate
  unrestricted selected-family candidate. The selected route uses
  owner splitting and a single triangle-free EHN selected-family file.
- Fixed the direction of the cyclic-successor equality in
  `Track1OwnerSplitGirth` to match the nonfixed-point goal.
- Corrected the focused checker to compile its imported modules
  before trying `lake env lean CheckTrack1.lean`.

**No Lean module or PR was merged, no green validation marker promoted,
and no GitHub Actions build was launched.**

## CI attempt (14 November, current)

Draft [Lean PR #1069](https://github.com/janhubicka/lean-girth/pull/1069)
requests an exact-head compiler run on this branch. GitHub's full Lean
workflow is separate from the broken manuscript TeX Action.
CI status must be checked at the *current* PR head SHA: a previous
queued run on an older SHA is not evidence for newer edits.
The new `Girth/Track1SelectedOldStrong.lean` bridge supplies the
old physical-edge support-reflection hypothesis directly from
an actual A-strong selected B-embedding, provided the retained
edges really are A-copies. This remains an uncompiled candidate.

## Continued validation after merging the global-bottom version

The manuscript's marked-isolated vertices now use one global tag
`(x,⊥)` (merged PR #457), matching the checked
`ColouredOwnerSelectedCopy.lift`. A reproducible finite regression
of precisely that variant was merged in girth PR #458;
**309,549** bounded cases passed, including marked isolated sources.
The previous private-tag finite tests should not be mistaken for a
test of the merged shared-bottom representation.

New candidate `Girth/Track1SelectedOldStrong.lean` proves that the
owner-splitting library's old-edge strongness input follows from
a genuine A-strong selected B-image and the fact that retained edges
are actual A-support copies; a second theorem composes this with
the existing checked selected-strongness result.
New candidate `Girth/Track1SelectedMixedLF2.lean` composes the
existing checked mixed-pair forest theorem with its actual-owner
transport, without pruning any ambient A-edge.
These files have focused `#print axioms` probes but **have not
yet been compiled**. Their remaining hypotheses must be supplied
from the exact selected EHN family and the actual picture attachment.
Draft Lean PR #1069 is the ongoing compiler gate, not a certificate
until its exact-head runs are verified.
