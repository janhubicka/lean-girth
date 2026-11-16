# Numbered Track 4 — standalone local \(F_{\mathbf t}\) witness audit (16 November 2026)

Status: **source-level mathematical audit, not kernel verification**. Companion manuscript change: girth PR #448 (local witness preparation lemma in \`paper/14-conversion.tex\`). Lean branch: PR #1064. The 190 registered axiom checks have not run; do not merge this draft or promote OPEN manuscript validation marks.

## What follows from the *stated* abstract forest assertion

The source is \`girth/paper/10-cycle-conditions.tex\`, \`def:principles\`, together with the train definition in \`paper/09-trains.tex\`.

1. **Fine-part relabelling.** For the true induced active system \(P=\Pi[e]\), take the parts above the processed base edge \(e\) as new, separate unary predicates. Each physical \(A\)-edge lies over the same ordered base \(A\)-copy and has the same refined coloured edge type. The original edge and labelled wagon sets do not change. Their allowed intersection predicates are pulled back to these fine parts. Applying \(F_{\mathbf t}\) to the refined train yields an \(e\)-partite local train; empty parts outside \(e\) extend it to a \(D\)-partite system. **Formal identification with the existing \`Partite.System\` representation is still missing.**
2. **Nonempty vertex-covering support.** A train is a nonempty hypergraph without isolated vertices, so its physical \(A\)-edges cover its entire vertex set. No inference \`IrreduciblesExtendTo A H\` is needed or licensed.
3. **Mixed forest and ordinary girth.** The \(F_{\mathbf t}\) forest clause includes all ambient one-edge members; hence distinct ambient edges cannot intersect in more than one vertex, and a Berge cycle of at most \(q\) ambient edges would be a forbidden nonforest mixed family. Thus \(H\) is \(A\)-linear and has ordinary support girth \(>q\). This is NOT the selected bottom \`FullSystemGirthGT q\` statement.
4. **Selected carrier injectivity.** Each selected train embedding \(f_i:P\to H\) is strongly induced and each vertex of \(P\) belongs to a physical \(A\)-edge. Therefore the complete \`bSupportPiece A (f_i)\` has exactly the vertex carrier of its image; the two different source edges remain distinct. Strong inducedness implies that equal carriers yield equal induced image copies, and the one-embedding-per-image convention rules out repeated indices. This yields exactly the required injectivity, not just injectivity of the embeddings.
5. **Exact trains.** Selected train embeddings reflect as well as preserve every wagon equivalence. The checked \`sharedCore_train_iff_of_prescribedRestriction\`, reused by \`TrainCoverageFreeExactLocalTrain.lean\`, is the necessary two-step physical restriction bridge. Do not substitute an unspecified preservation-only property.
6. **Positive bounds, parameters and arrow.** \(F_{\mathbf t}\) supplies full system girth at the actual positive proper cuts, adjacent-part parameters and a PHYSICAL-edge colouring arrow on selected images. The ordered source/partite uniqueness identifies each physical \(A\)-edge with its relational ordered \(A\)-embedding, provided the fine-to-coarse type correspondence is proved. There is no additional embedding-colouring Ramsey assumption.

## Remaining *nontrivial* theorem, not an admissible new axiom

For every ready coverage-free \`ForestStage\` and every genuinely nontrivial true active fibre \`e\` (two different physical \(A\)-carriers), start with its PROVED same-vector active labelled wagon girth (\`TrainCoverageFreeTrueActiveGirth.lean\` / \`TrainCoverageFreeFtEligiblePass.lean\`), invoke the abstract \(F_{\mathbf t}\) on the recoloured actual active train and *construct* the concrete local data for \`ForestStage.orderPictureStep_of_nontrivial_Ft\` (\`TrainCoverageFreeNontrivialFtStep.lean\`). The construction must yield, rather than assume:

- the finite \`Partite.System\` over \(D\), the index family and \`IsPartiteOver D\`;
- physical A-support nonempty and covering every vertex;
- selected complete-support injectivity and the genuine finite mixed SET forest through the same \(q\);
- exact old/shared/local wagon relation at **all** levels; adjacent parameter coarsening;
- the positive \`activeGluingWitnessOrderOneData.FullSystemGirthGT\` certificates at every proper \(h_j\);
- rigidity and the indexed PHYSICAL-edge Ramsey arrow, with the selected witness index preserved.

Then the prepared nontrivial step plus the identity step for 0/1 physical fibres and \`TrainCoverageFreeInitialFinitePass.lean\` prove the selected final strong train arrow. The source currently assumes this local operator: it has NOT proved its existence from an abstract \(F_{\mathbf t}\) predicate.

## Additional checks / cautions

- At \(q=2\), the local bottom system-girth bound is **not** a consequence of a pairwise mixed forest. The auxiliary order-two certificate is at the universal TOP, as in \`TrainActualCutoffTwoFromMixed.lean\`, and must be checked independently.
- The nine-vertex \(K_4\) obstruction applies to generic relational A-irreducible coverage; it is NOT claimed as an obstruction for the paper's special coloured one-edge type. No stronger coverage property is used.
- Source-only bottom original length-two preservation, the selected-piece segment lemma, and the two full preservation branches still require exact-head Lean elaboration/axiom inspection. Comments asserting a new theorem is “checked” do not establish kernel verification.
- The source-level preparation lemma makes the missing fine-part local-choice bridge explicit, not settled. The original theorem statement remains OPEN.

### Minimal next kernel sequence

First compile the *existing* pinned dependencies and \`TrainCoverageFreeNontrivialFtStep.lean\`. Next implement and compile the witness relabelling/support/selected-family bridge (separate module, avoiding a new “localFt” oracle); then \`TrainCoverageFreeInitialFinitePass.lean\`, \`CheckTrack4MinimumOwnerSwap.lean\`, and inspect every \`#print axioms\` result at the exact new head.