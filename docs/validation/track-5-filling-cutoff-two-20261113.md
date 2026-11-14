# Numbered validation Track 5 — current audit (14 November 2026)

**Scope:** canonical filling; direct cutoff-two construction from the
individual first wagons; exact labelled Ramsey arrow; preservation of
all proper-cut full system-girth bounds. Numbered issue #1056, programme
#1060. This is **not** the legacy lettered Track C.

**Frozen source used for comparison:** girth/main at
`8c9cfa6eb6d817a08f3009fe048fc0be07426ece`, digest
`45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
New manuscript edits are in **draft** girth PR #450;
candidate formalization is in **draft** lean-girth PR #1063, based on
lean-girth/main `98e40142f95cf818f498ed21faf9302a50fe7832`.
Both PRs remain UNMERGED and no new Lean validation marks are warranted.

## What the actual proof needs

Write `W = ⨆ₚ Fₚ` for the disjoint union of the first wagons of the
original train T. The first EHN arrow chooses one `s : W ↪ X`.
For every p use `sₚ = s ∘ uₚ : Fₚ ↪ X`; **do not** identify each
`Fₚ` with all of W, or choose unrelated embeddings for the
different first wagons. The component `Mₛ` contains one contracted
first-wagon edge `fₛₚ` with the complete X-coordinate set. M is the
vertex-disjoint union of the `Mₛ`, with all proper train relations
componentwise and only the universal top shared.

After applying the shorter `RR_h` with full X-edge colour words,
each selected old parent `j : M ↪ N` gives a complete filling
`j[X] : M[X] ↪ N[X]`. The designated targets are the **labelled
pairs (j,s)**. Their sibling choices under the same j are disjoint;
different old parents j may overlap. **Never delete** unselected
ambient N or N[X] edges.

The exact physical colouring calculation is:
`χ(ι_{j[fₛₚ]}[sₚ(e)]) = χ_{j[fₛₚ]}(sₚ(e)) = ρ(sₚ(e)) = c`
for every original target edge e, with ONE old parent j, ONE selected
W-copy s and the SAME complete word ρ across every first wagon.
The final conclusion must be about the actual designated family,
not merely an arbitrary monochromatic edge subset.

## Reused existing Lean (do not re-prove)

- `TrainFillingTemplateConstruction`: canonical physical edge
  equivalence, unique old cover and generated-edge linearity.
- `TrainFillingPrivateExtension`: exact private-vertex intersections,
  original target containment and local scattering geometry.
- `TrainFillingIndexedActualMPhysicalTrain`: actual contracted
  M-support-to-physical-edge equivalence and faithful train cuts,
  **conditional on the specific support equality**.
- `TrainFillingIndexedSelectedPhysicalMap`: full physical
  heterogeneous G0-to-H edge embedding and range, no pruning.
- `TrainFillingIndexedMonotoneCarrierBridge`: finite uniqueness
  of increasing coordinate placements, yielding all filled-edge
  carrier equalities from full old carrier equality.
- `TrainRecursiveWitnessPass` and
  `TrainFillingSelectedStageTrainReflection`: actual selected
  shorter-stage M-copies, their physical old A-edge maps and
  preservation **and reflection** at every train cut.
- `TrainFillingOrderStageCanonicalAllCutGirth`: for the actual
  **OrderStage**, all proper old cuts have full system-girth
  bounds, INCLUDING the old equality cut. Use its canonical
  filling theorem, not the weaker bare ForestTailStage tail bounds.
- `TrainFillingIndexedParentwiseRealization`,
  `TrainFillingIndexedFaithfulParentwise` and
  `TrainDesignatedSubcopyGirth`: global scattering preserving
  ALL ambient edges, no cross-parent disjointness assumption.
- `TrainFillingIndexedSelectedColourWord`: literal two-arrow
  filled edge-colour identity; used with the true selected b below.

Prior Lean verification of these older modules is **not** a
certificate for any candidate added in this PR.

## New *candidate*, uncompiled bridges in PR #1063

1. **Unequal first wagons:** `PrivateSummand`,
   `PrivateSelectedUnion`, `PrivateSelectedColour`,
   `PrivateSelectedFamily`, `PrivateSelectedIndexedArrow` and
   `PrivateEHNArrow`. These construct local private embeddings of
   different types `Fₚ` from ONE selected `s(W)`, derive
   A-strongness by composition, supply complete common X support,
   and derive the exact local `selectedCommonEdges` Ramsey arrow
   from the genuine EHN closed-target arrow. The real assumptions
   `A ↪ W` nonempty and local vertex coverage remain visible.

2. **Genuine lower selected parent:** `PrivateStageSelectedPhysical`,
   `PrivateSelectedStageFilling`, `PrivateSelectedOldRange` and
   `PrivateActualOrderParent`. They construct βⱼ from the selected
   `OrderStage` copy **j itself**, rather than postulating a new
   injection. The full old-edge image is exactly the ambient A-support
   edges contained in j(M), and all proper-cut relations are
   preserved/reflected through that SAME βⱼ.

3. **Actual filling and scattering:** `PrivateCanonicalParentwise`,
   `PrivateCanonicalCutBridge`,
   `PrivateActualOrderRealization` and
   `PrivateActualOrderStrictMono`. These construct the actual
   parentwise vertex/edge maps, full copy-edge range and quotient
   wagon maps for **all** selected j, then identify the resulting
   incidence data with the canonical inherited cut. The primary
   interface uses exact *edge carrier images*, not arbitrary
   separately assumed output wagon maps or pointwise coordinates.
   The new strictMono theorem derives the carrier images from full
   first-wagon carriers plus source, selected-copy and canonical
   placement order compatibility. The new
   `canonicalFilledSelected_targetFullSystemGirthGT_of_inherited_carrier`
   transfers the old full bound to the same target family without
   assuming output girth.

4. **The true labelled arrow:** `PrivateActualWordArrow` first
   pulls a full old N-edge colour word back to actual A-embeddings,
   then returns the genuine selected j (not just an abstract β).
   Its source A-copy is derived from a nonempty index
   `C × P`; it is not an unrelated default-colour assumption.
   `PrivateActualIndexedArrow`,
   `PrivateParentwiseColour` and
   `PrivateActualLabelledArrow` combine that selected j with
   the ONE EHN s to obtain monochromaticity on the *actual*
   `designatedFamily.target.copyEdges (j,s)`.

5. **Exact-head check gate:** `Girth/CheckTrack5Private.lean`
   contains targeted `#check` and `#print axioms` probes. It
   **has not been executed** on the new branch. No new theorem
   has been kernel checked, nor have all elaborated hypotheses
   been audited.

Unused pointwise-placement wrappers, an unindexed Ramsey-arrow
projection and a standalone restored-wagon wrapper were removed
from the draft to reduce duplicated interfaces. Later claims
must use the stronger parent-indexed and carrier-only declarations.

## Adversarial issues and corrected source

**Important falsifier: old edge linearity does NOT imply first-wagon
carrier linearity.** The graph with edges
`ab, ac, bd, cd` is linear, but first wagons
`F₀={ab,ac}` and `F₁={bd,cd}` share both b and c.
Private contraction would therefore have two old common vertices,
contradicting linearity. The actual cutoff-two assumption
`girth(W₁(T)) > h₁ ≥ 2` forbids this labelled two-cycle.
The manuscript preliminary lemma now *states* the required first
wagon carrier linearity and the application *derives* it. It
also explicitly requires ≥2 vertices in each template X-edge
for uniqueness of the old cover (automatic for the coloured
edge type under discussion).

The common-edge arrow was fixed after discovering an incorrect
attempt to treat a transported `CommonTemplateEdge` as a member
of the original local selected-edge subtype. The proof now uses
the actual local selected element first and transports it
through `choiceTemplateEquiv`.

The manuscript had a literal `\\nFor` inside the canonical
filling statement; that TeX command was corrected to a real
newline. The disjoint union M now explicitly tags every
vertex by s, including old target vertices.

## Executed bounded regression (NOT a general formal proof)

Local `/mnt/data/track5_private_smoke.py` ran successfully:
- Two unequal Fₚ: three versus four original vertices.
- Disjoint-union W: seven vertices and five original edges.
- Two selected X-copies: fourteen template vertices, ten template
  edges, four contracted first-wagon edges, forty filled edges.
- Two selected old parent copies whose images SHARE one vertex;
  the FULL ambient N has eight old edges and its filling has
  **80 physically distinct edges**, retaining all unselected edges.
- All four labelled `(parent,choice)` target edge families retain
  their original edges, are strongly induced and satisfy the
  appropriate complete colour-word calculation. Sibling choices
  remain disjoint, while cross-parent overlap is allowed.
- The four-edge first-wagon-carrier counterexample is reproduced.

This is a finite sanity check, NOT an EHN theorem, Ramsey arrow
for arbitrary colourings, Lean verification or proof of general
full system girth.

## What actually remains to close `lem:tailraw`

1. Instantiate the **ordered, partite**, actual colour-block
   relational M of the selected unequal-summand family.
   Discharge all `hColour`, `hCoordinate`, `hXBlocks`,
   `hSupport`, old-carrier linearity and target order hypotheses
   of the existing actual M-support and ordered-carrier lemmas.
2. Supply the genuine shorter `RR_h` witness as the required
   *selected* `OrderStage` with its `DesignatedArrow` and
   `allCutGirth`. The abstract formal OrderStage alone does
   not assert global `StrictMono` for every selected embedding;
   establish that from the actual block-ordered colour language,
   or choose the correct ordered presentation instead of assuming it.
3. Identify the ONE canonical full support filling N[X] and its
   inherited train with the concrete `OrderStage` input at each
   old cut. Apply `OrderStage.canonicalFilledCut_fullSystemGirthGT`
   and the carrier-only parentwise/scattering lemmas, **not** a
   new or circular output-girth assumption.
4. Identify each selected `(j,s)` target with an actual copy of
   the ORIGINAL T, preserving every part, order and train relation.
   The candidate labelled monochromaticity lemma establishes
   only the edge-colour part until this is done.
5. Perform a local *exact-head* Lean build, then inspect
   `#print axioms`, hidden universes and every proof hypothesis.
   Build the full TeX to certify all source changes. This container
   has no Lean/lake/elan binary, its git process cannot resolve
   github.com, and the 2026-11-08 prebuilt Lean/mathlib bundles are
   not mounted. We have **not run** a kernel check or paid GitHub
   Actions. The PRs must stay **draft and unmerged**.

**No new validation mark is justified.** This is an adversarial
source audit and an explicit, testable integration plan.


## 14 November further adversarial repair: keep ordered EHN witnesses

**New precise flaw in the previous local EHN adapter:** the existing
\`closedTargetRamseyFamily_of_monotone_embeddings\` proves its Ramsey
arrow by first taking an **ordered** EHN target embedding, then
forgets the auxiliary linear-order relation when it returns a
\`ClosedTargetRamseyFamily\`. The final exported type quantifies
over closure embeddings with no strict monotonicity certificate.
Therefore indexing the private choices by **all** such embeddings
does *not* by itself prove the \`hCoordinate\` hypotheses needed
by \`actualIndexedContractedM_support_eq\`.

Candidate repair, still uncompiled:

- \`TrainFillingPrivateMonotoneEHN.lean\` retains the genuine
  increasing EHN-selected embedding as part of a stronger
  \`MonotoneClosedTargetRamseyFamily\` statement. It follows
  the already checked ordered EHN proof without adding a
  Ramsey-theoretic assumption; the ordinary result is obtained
  by forgetting the certificate.
- \`TrainFillingPrivateMonotoneSummands.lean\` indexes choices
  only by the genuine closed embeddings **with** a
  \`StrictMono\` certificate, not every closure embedding.
  It derives monotonicity of all individual
  \`s_p = s ∘ u_p\` coordinates from the increasing component
  inclusions and derives the one-common-colour EHN local arrow
  on this restricted index family.
- \`TrainFillingPrivateMonotoneExistence.lean\` combines the
  ordered EHN theorem and these unequal-summand constructions
  into a single existence statement with a common full X-edge
  family, increasing local coordinates and the actual indexed
  local Ramsey arrow.
- \`TrainFillingPrivateColourBlockOrder.lean\` constructs the
  **colour-first, old-order-second** total order by
  \`LinearOrder.lift'\` through \`I ×ₗ X\`. It proves
  the missing \`hXBlocks\` property and proves that
  a colour-preserving increasing W→X embedding remains
  increasing after colour-block sorting, either just X
  when W already has blocks, or BOTH W and X. This
  does **not** assert that an arbitrary functional EHN
  closure embedding preserves the colours: that must
  be derived from the concrete unary predicates when
  instantiating the ordered relational target.

**Separate uncovered-vertex issue:** \`ElementaryCAClass A R\`
means A-linear reduct plus canonical binary closure c_A;
it does NOT assert that every vertex of the produced EHN X
lies in an A-copy. The paper uses a **covered** witness X,
so the formal interface must either produce this genuinely
or explicitly trim X after the EHN selection.

\`TrainFillingPrivateCoveredEHN.lean\` now proves:
  (1) the union of all A-support edge carriers has no uncovered
  vertices by definition, and each original edge is contained;
  (2) if each original F_p is A-covered and the component
  inclusions cover W, then W is A-covered; and
  (3) every chosen W→X image survives entirely in the
  A-supported vertex reduct, with no loss of an original edge.
The **full induced-structure retyping and Ramsey-arrow transfer**
to the covered vertex type is **still open**. No coverage of the
original C is assumed.

**Parent strongness:** a new candidate
\`TrainFillingPrivateActualParentStrong.lean\` derives
\`actualOrderParent_filledEdges_eq_contained\`: the full
filled-edge image of a genuine selected lower M-parent is
EXACTLY the set of ambient H-edges contained in its
selected vertex carrier. It uses the already checked
\`UniformFillingData.selectedFilledEdgeEmbedding_range_eq_contained\`,
the actual selected old support range, old
\`OrderStage.strong\`, and the two-vertex template condition.
No output girth or arbitrary output strongness appears.

All new declarations have been added to
\`Girth/CheckTrack5Private.lean\` with appropriate
\`#check\`/\`#print axioms\` probes. These probes have
**not** been executed in Lean. Source-level delimiter/import
checks are not kernel verification.

### Current outstanding gates, not assumptions

1. Produce the **actual relational disjoint union** W with
   selected increasing component inclusions, full A-coverage
   and the correct unary predicates/within-colour orders.
2. Retype the EHN-selected family to the **covered** X
   support (preserving the arrow), then derive the actual
   vertex colour function from the unary relations. Sort
   the X order by colour blocks, preserving selected monotonicity.
3. Instantiate the checked real coloured-order M support
   theorem and the genuine shorter \`RR_h\` OrderStage with
   the exact same X, selected choice family, support and
   global partite order.
4. Identify the actual canonical filled parent cut with
   \`OrderStage.canonicalFilledCut_fullSystemGirthGT\`;
   complete the selected labelled T embedding (all parts,
   orders and wagon relations) in addition to the candidate
   monochromatic edge statement.
5. Obtain an **exact-head local Lean build** and axiom
   audit, and a full TeX compile; until then no
   verification marks or PR merges.

This is a **correctness repair** to the EHN application
interface, not a new hypothesis of the mathematical theorem.
It avoids the invalid shortcut "all closed copies are ordered"
and does not reintroduce any requirement that
\`F_p ≃ W\`.


### Upstream Track 1 dependency checked against newer main (14 November)

The manuscript has advanced beyond the original frozen source:
[girth PR #454](https://github.com/janhubicka/girth/pull/454),
[#455](https://github.com/janhubicka/girth/pull/455), and
[#456](https://github.com/janhubicka/girth/pull/456)
have been merged on main. The Track 5 draft still bases its
two edited inputs on the pinned 41-page source and is kept
separate, currently mergeable but UNMERGED. Those Track 1
merges do **not** constitute a new Lean certificate.

In the currently merged \`paper/04-coloured-edges.tex\`,
\`lem:markededgesplit\` has an explicit necessary hypothesis:

> A vertex of the coloured target B in a predicate outside the
> chosen allowed set S is incident with at most ONE edge of B.

For the cutoff-two application B=W (the tagged disjoint union
of first wagons), this condition is **derived**, not assumed:
inside each F_p, the train parameter A_1 allows two original
edges to meet only in A_1 predicates, and no edges cross the
disjoint summands W. A vertex of W in a predicate outside A_1
therefore lies in at most one edge. The Track 5 manuscript
now says explicitly why \`lem:unrestricted\` applies with
S=A_1. If this marking condition were omitted, the claimed
first parameter of X would not follow just from an arbitrary
A-linear functional EHN output.

The newer Track 1 manuscript obtains the entire **covered,
ordered, parameter-restricted** X from:
1. an unmarked functional EHN witness with an actual
   increasing selected family;
2. the owner-splitting construction that retains only selected
   target edges/vertices and splits vertices in forbidden
   predicates; and
3. the colour extension argument preserving the arrow and
   labelled chosen copies.

Track 1 issue [#1052](https://github.com/janhubicka/lean-girth/issues/1052)
still reports its full ordered selected-family/owner-splitting
Lean proof as OPEN. Therefore our new Track 5 modules
\`PrivateMonotoneEHN\`, \`PrivateColourBlockOrder\` and
\`PrivateCoveredEHN\` should be understood as **reusable
preparation**, not an independent replacement for the entire
\`lem:unrestricted\` witness with its \`A_1\` parameter and
all selected incidence properties.

**Coordination boundary:** Do not duplicate or diverge from the
Track 1 owner-splitting argument on this branch. Once its
exact selected-order/marked-splitting bridge is kernel-checked,
use it to supply the missing covered X and the permissible
EHN choices in the actual Track 5 shortened M.
