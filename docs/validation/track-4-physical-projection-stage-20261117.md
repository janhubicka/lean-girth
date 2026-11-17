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
