# Numbered Track 4 — physical-copy projection and stage refactor (17 Nov 2026)

**STATUS: SOURCE-LEVEL CANDIDATES, UNCOMPILED. Do not merge PR #1064 or promote circulation validation marks.**

The old coverage-free \`ForestStage\` correctly dropped the recursive \`mixedCoverage\` field, but still required \`stage.isPartite : stage.system.IsPartiteOver D\` in the **full ordered relational language**. That condition is not a consequence of the abstract F_2 forest assertion; see [the explicit order-triangle obstruction](./track-4-q2-ordered-partiteness-obstruction-20261116.md).

## A sufficient geometric invariant

\`ProjectsACopies A D C\` says:

\`∀ a : Embedding A C.toRelStructure, ∃ b : Embedding A D, ∀ x, b x = C.part (a x)\`.

It only projects *genuine physical A-copies*. There is no requirement to reflect the binary order on arbitrary irreducible induced ambient sets.

The new \`Girth/TrainCoverageFreeACopyProjection.lean\` supplies four independent source-level proof candidates:

1. Full \`IsPartiteOver\` entails \`ProjectsACopies\` (never conversely).
2. An A-partite fine-coloured F_t core whose physical A-embeddings use exactly the prescribed fine parts satisfies \`ProjectsACopies\` after relabelling by the processed base A-embedding.
3. Every embedded irreducible A-copy of a free attachment factors through the core or one attached standard; consequently \`ProjectsACopies\` is preserved by free attachment.
4. The standard active-carrier A-strongness proof uses only the image of the **physical** A-copy in the A-linear base, plus rigidity of the processed base copy; no full \`IsPartiteOver\` is needed. The same condition supplies the base embedding for each nontrivial projected fibre.

The proof of (3) uses \`RelStructure.Attachment.irreducible_core_or_copy\` and \`Embedding.factorThroughRange\`; it is not a new Ramsey lemma.

## Downstream proof obligations reduced

- \`TrainCoverageFreeACopyGeometry.lean\`: old-picture A-copy projection gives exact strong-gluing geometry and the exact support equality of the true active induced subsystem with its projected physical A-edges.
- \`TrainCoverageFreeWeakProjectionGirth.lean\`: ports the **full positive original B-labelled** one-level system-girth transfer. The source theorem's \`IsPartiteOver\` was used only to derive active A-strongness; the replacement uses the weaker projection result.
- \`TrainCoverageFreeACopyGeometry.lean\` also keeps \`PartiteOrderCompatible\` independent of \`ProjectsACopies\`, and proves the **pair** survives free attachment by reusing the checked separate order-compatibility theorem. One invariant does not imply the other.
- \`TrainCoverageFreePhysicalStage.lean\`: new \`PhysicalForestStage\`/\`PhysicalOrderStage\` replace the overstrong \`isPartite\` field with \`projectsACopies\`; otherwise retain all selected original B labels, physical A-support, finite mixed SET forests, train restrictions, adjacent-part parameters, positive full system girth and strongness. There are genuine forgetful constructors from the old stronger stages, but no inverse.

## Finite pass (source-only)

The following modules port the checked finite selected Ramsey combinatorics to the weaker physical-stage types:

- \`TrainCoverageFreePhysicalFinitePass.lean\`;
- \`TrainCoverageFreePhysicalOrderPass.lean\`;
- \`TrainCoverageFreePhysicalFibrePass.lean\` (the nontrivial case uses \`baseEmbedding_of_projectedACopy\`, not the old strong partite bridge);
- \`TrainCoverageFreePhysicalStrongFinitePass.lean\`;
- \`TrainCoverageFreePhysicalTrueActiveGirth.lean\`;
- \`TrainCoverageFreePhysicalFtEligiblePass.lean\`;
- \`TrainCoverageFreePhysicalInitialFinitePass.lean\` (forgets the extra old initial-stage partite certificate while retaining genuine bottom girth and selected base lifts).

The finite pass is **conditional on genuine local PictureSteps**. The old and new proof bodies are text-identical under renaming for the core order/strong/girth/F_t eligible passes; the fibre dispatcher replaces exactly one previously overstrong base-embedding bridge, and the initial-stage constructor additionally forgets the strong partite certificate.

Static audits found no \`sorry\`/\`admit\`/\`axiom\` in these new modules, no unresolved \`Girth.*\` imports, and no unmatched delimiters. These checks neither elaborate Lean terms nor certify \`#print axioms\` output. The checker \`CheckTrack4MinimumOwnerSwap.lean\` now registers **237** axiom checks, **zero executed**.

## Remaining genuine integration

1. **Most important:** port the **actual local physical attachment and bottom forest increment** to \`PhysicalForestStage\`. In the earlier \`TrainCoverageFreeBottomIncrement.lean\`, the checked \`actualPartiteDesignatedAB_forest_and_girth_of_localGeometry\` still receives \`stage.isPartite\`. Refactor that specific geometric premise through \`activeCarrier_aStrong_of_projectedACopies\` rather than assuming it back. The new stage itself is not yet a completed recursive step.
2. **Raw F_t output:** construct the locally relabelled physical core, selected train embeddings, mixed SET forest, exact positive full bounds and physical-edge indexed arrow from the abstract forest assertion. Existing \`RawPartiteFtWitness\` is conditional and still contains the overstrong **ordered** \`IsPartiteOver\` field; it is not the replacement.
3. **Auxiliary orders:** keep \`PartiteOrderCompatible\` as an independent invariant during attachments; keep within-part orders *outside* the relational free-amalgamation reduct, and extend them at the final pass. \`PhysicalForestStage\` alone does not currently store this order-compatibility proof. In particular a \`Partite.System L.withOrder\` must NOT encode comparisons between two different vertices in the same fine part, since its transversal condition rules them out.
4. **Validation:** no matching Lean/lake/elan and pinned dependencies exist in the current container. Exact-head compilation, all printed axiom results, semantic adversarial audit and LaTeX build are still outstanding. Keep both PRs draft, and leave \`thm:preservation\`, \`cor:coordinate\`, \`prop:globalize\` OPEN.

**Manuscript:** \`girth\` PR #448 now has \`lem:physicalprojection\`, including the free-attachment and separate order-compatibility proofs, before the local forest witness preparation lemma. This is a proof-organization simplification rather than a new assumption.


## Second continuation — actual physical bottom and raw witness chain

**Source as of 17 November, still UNCOMPILED.** The previously missing genuine physical attachment has now been ported, rather than assumed as a finished local PictureStep.

### Exact dependency chain

- \`ForestActualACopyTestedBoundaryWeak.lean\`: a genuine attached physical A-copy lies in the core or is a tested transported old A-copy with the true small/whole boundary. The only changed input is \`ProjectsACopies\` in place of \`IsPartiteOver\`.
- \`ForestActualRecursiveIncrementWeak.lean\`: the original factored-canonical selected mixed forest proof, using the weak physical boundary theorem. All old selected B labels and all actual A-edge members are retained.
- \`ForestRecursiveOutputGirthWeak.lean\`: the genuine selected bottom forest/ordinary output girth, replacing the two uses of strong partiteness with weak active A-strongness and weak mixed ownership.
- \`TrainCoverageFreePhysicalBottomIncrement.lean\`: bottom selected B/A forest, ambient A-support girth and all selected B strongness on a \`PhysicalForestStage\`.
- \`TrainSelectedPictureIntrinsicGeometryWeak.lean\` and \`TrainCoverageFreeWeakProjectionGirth.lean\`: all-level physical wagon strongness/linearity and positive original B-labelled full system-girth transfer without ordered strong partiteness.
- \`TrainCoverageFreePhysicalAttachment.lean\`: a **genuine** next \`PhysicalForestStage\`, selected transitions, indexed picture step and \`ActiveAttachmentBounds\` requiring only core \`ProjectsACopies\`.
- \`TrainCoverageFreePhysicalBoundsFromMixed.lean\`, \`TrainCoverageFreePhysicalForestOrderStep.lean\`, \`TrainCoverageFreePhysicalPositiveTransfer.lean\`, \`TrainCoverageFreePhysicalNontrivialFtStep.lean\`: same-q mixed forest plus q=2 universal-top certificate, literal positive full-system girth and actual selected OrderStage/PictureStep from explicit local forest data.
- \`TrainCoverageFreePhysicalDirectPartiteFtStep.lean\`: a direct local F_t core uses **fineEdges** (\`∀ a : Embedding A H, ∀ x, H.part (a x) = x\`) to prove \`ProjectsACopies\` after relabelling; **no** \`H.IsPartiteOver A.ordered\` assumption.
- \`TrainCoverageFreePhysicalRawFtWitness.lean\`, \`TrainCoverageFreePhysicalRawFtFinitePass.lean\`: the explicit raw forest witness record and conditional initial-to-final strong selected train Ramsey result. The local existence premise is the expected data of F_t, not a ready-made next-stage PictureStep.

The original bottom forest, selected mixed forest and all-level intrinsic-geometry proof bodies were independently compared against the weak ports. After mechanically replacing the **identified partite-premise calls**, the bodies were text-identical in the checked comparisons. This supports faithful porting; it does **not** establish Lean elaboration.

### Separate auxiliary order invariant

\`TrainCoverageFreeACopyGeometry.lean\` now proves that forward \`PartiteOrderCompatible\` survives both fine-part relabelling and free attachment, independently of physical-copy projection. \`TrainCoverageFreePhysicalAttachment.lean\` adds \`PhysicalForestStage.activeAttachment_orderCompatible\`; given actual old/core auxiliary compatibility, the genuine next physical stage retains it.

**This does not say arbitrary F_t automatically supplies the local order-compatibility proof.** The current raw record models \`L.withOrder\` as a partite relational structure, while the English F_t treats within-part orders as auxiliary. A faithful order-reduct / auxiliary-order bridge, initial compatibility and final order completion remain obligations. \`PhysicalForestStage\` currently does not store a compatible-order certificate.

### Static and kernel status

- The source-level ports remove the problematic old \`stage.isPartite\` and \`bounds.corePartite\` uses from the **physical** bottom/positive/direct modules. The older alternative strong-stage modules remain unchanged for comparison.
- Focused source scans found balanced delimiters, no literal proof holes (\`sorry\`, \`admit\`, or new \`axiom\`) and all declared \`Girth.*\` imports rooted in existing files; no exact-head Lean/lake build has been executed.
- \`CheckTrack4MinimumOwnerSwap.lean\` now registers **262** \`#print axioms\` checks (the previous figure of 237 is historical), **none executed**.
- No theorem is kernel-certified by these source changes. No validation marker has been promoted and no TeX/PDF build is claimed.

### Remaining proof obligations

1. Translate the manuscript's **abstract universal F_t** (coloured edge type, auxiliary fine-part orders, selected embeddings, mixed forest, positive full system bounds and indexed edge Ramsey arrow) into the concrete \`Physical.RawPartiteFtWitness\` existence statement without losing labels or adding order assumptions. This is mathematical type/representation work, not a missing local picture-step oracle.
2. Maintain forward inter-part order compatibility and separate within-part orders through the actual finite pass, with a final linear extension that preserves the original ordered target and does not introduce spurious physical A-edges.
3. Perform exact-head Lean elaboration/CI under the pinned dependencies and inspect all 262 axioms; then adversarially recheck the q=2 and original B-labelled length-two cases. The manuscript's \`lem:physicalprojection\`, \`lem:localforestwitness\`, \`thm:preservation\`, \`cor:coordinate\`, \`prop:globalize\` remain marked OPEN as appropriate.

**Both manuscript PR #448 and Lean PR #1064 remain DRAFT; DO NOT MERGE.**
