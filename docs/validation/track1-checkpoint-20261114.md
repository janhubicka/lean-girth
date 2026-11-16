# Numbered Track 1 — certified kernels and remaining proof (15 November 2026)

Supersedes the provisional 14 November status. A **kernel certificate for an
individual lemma** is not a certificate of the complete local-forest theorem.

## Exact-head Lean certificate

- Foundational [lean-girth PR #1069](https://github.com/janhubicka/lean-girth/pull/1069):
  kernel-tested at `f24cb19d364d31e54867f037e93f51695ca6aaab`, then
  **merged** as `733d3c80e2d86feb5d2721fa85300088297e00a7`.
- [Lean run #43689961389](https://github.com/janhubicka/lean-girth/actions/runs/43689961389)
  **SUCCESS** on 15 November: full project-module compilation, all registered
  theorem-axiom checks, and the finite boundary regressions.
- In particular, `CheckTrack1.lean` printed **18 axiom sets**.
  The repository's strict `scripts/check_axioms.py` accepted only
  `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
- Manuscript simplifications merged in girth PR #454, source checker in
  #455, finite strong-amalgam regression in #456, global bottom-tag
  correction in #457 and matching finite regression in #458.
  The author compiles TeX manually.

## Statement-by-statement validation status

| Paper item | Existing Lean evidence | Remaining proof obligation |
| --- | --- | --- |
| `lem:closedamalgam` | One-step A-linearity and both strong-side conclusions in `ElementaryClosureAmalgam`; newly verified `Track1StrongAmalgamGirthThree.track1_girthGT_three_freeAmalgam_of_aStrong` | Finite successive attachment follows by straightforward iteration; no separately named iterated Lean theorem |
| `obs:functionalinput` | Existing `ElementaryCAClass_freeAmalgamationClass` and now verified `Track1TriangleFreeEHNClass.ElementaryCAThreeClass_freeAmalgamationClass` for canonical pair closure | The paper additionally claims arbitrary extra partial functions of fixed arity: that *general language adapter* is not established by this module |
| `lem:basedclosure` | Checked `TargetClosure.targetClosed_classify_nonempty` and `ClosureEmbeddingGeometry.targetEmbeddings_controlledIntersection` | No new target-closure language needed |
| `thm:AlinearRamsey` | Verified `Track1TriangleFreeSelectedFamily.track1_selectedOrderedRamseyFamily_triangleFree`, retaining the genuine fresh-order-respecting selected family, strong images, controlled intersections, its Ramsey arrow and girth >3 | Translate the chosen family to the exact coloured ordered one-edge presentation for its application |
| `lem:markededgesplit` and `lem:unrestricted` | Existing checked owner-splitting suite; new checked `Track1OwnerSplitGirth`, `Track1OwnerSplitCoverage`, `Track1OwnerSplitOrderArrow`, `Track1OwnerSelectedFromEmbedding`, `Track1SelectedOldStrong` | Assemble actual positive selected edges, one global order, full induced coloured B lifts, precise shared-edge intersections, covered vertex carrier and selected arrow. Draft PR #1074 is not certified yet |
| `lem:threeboundaries` | Verified `Track1CutoffThreeReuse.track1_three_boundaries_forest_of_core`, specializing the checked generic distinct-owner girth result | Supply exact small/whole-edge boundaries from an actual picture |
| `lem:threepicture` | Verified conditional `actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull` and `Track1SelectedMixedLF2.track1_actualMixedLF2_of_strong_controlled` | Actual selected physical owners, true-active maps, core girth, ambient linearity, and nontrivial target support needed to instantiate at m=3 |
| `prop:forestthree` | Above kernels and general partite component library | Actual intermediate picture assembly, backwards Ramsey fusion, part order and original isolated target vertex restoration; full statement NOT kernel-certified |

## Bounded diagnostics — not proof certificates

408,749 small strong free amalgams, 309,549 selected shared-bottom
splitting families, and 74,230 three-boundary configurations passed
their bounded tests. Mathematical proofs do not follow from enumeration.

## Unmerged work

- [Draft PR #1074](https://github.com/janhubicka/lean-girth/pull/1074):
  `validation/1-ordered-copy-packaging-20261115`, a conditional
  selected-owner assembly with `CheckTrack1SelectedAssembly.lean`.
  **Compiler/axiom verification remains pending**.
- `validation/1-actual-partite-interface-20261115`: continuation
  candidates for actual common A-edge membership in both selected
  B sources, source forbidden-degree-one, colour recovery from the
  witness's full unary relations, EHN family subtype indexing, the
  true old coloured-ordered selected presentation, and mixed-LF2.
  These remain **uncompiled**.

## Next verifiable steps

1. Check exact-head CI and strict axioms for #1074, then repair any
   actual compiler errors before merging.
2. Compile the next-step actual-partite adapters behind their own
   focused checker.
3. Supply true-active selected maps and the backward finite Ramsey
   fusion; instantiate the checked conditional picture increment at m=3.
4. Promote remaining manuscript markers only on genuine end-to-end
   certificates. The external EHN theorem remains an explicit input.
