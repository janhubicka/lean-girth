# Numbered validation Track 5 — current audit (14 November 2026)

**Scope:** canonical filling; direct cutoff-two construction from the
individual first wagons; exact labelled Ramsey arrow; preservation of
all proper-cut full system-girth bounds. Numbered issue #1056, programme
#1060. This is **not** the legacy lettered Track C.

**Frozen source used for comparison:** girth/main at
\`8c9cfa6eb6d817a08f3009fe048fc0be07426ece\`, digest
\`45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec\`.
New manuscript edits are in **draft** girth PR #450;
candidate formalization is in **draft** lean-girth PR #1063, based on
lean-girth/main \`98e40142f95cf818f498ed21faf9302a50fe7832\`.
Both PRs remain UNMERGED and no new Lean validation marks are warranted.

## What the actual proof needs

Write \`W = ⨆ₚ Fₚ\` for the disjoint union of the first wagons of the
original train T. The first EHN arrow chooses one \`s : W ↪ X\`.
For every p use \`sₚ = s ∘ uₚ : Fₚ ↪ X\`; **do not** identify each
\`Fₚ\` with all of W, or choose unrelated embeddings for the
different first wagons. The component \`Mₛ\` contains one contracted
first-wagon edge \`fₛₚ\` with the complete X-coordinate set. M is the
vertex-disjoint union of the \`Mₛ\`, with all proper train relations
componentwise and only the universal top shared.

After applying the shorter \`RR_h\` with full X-edge colour words,
each selected old parent \`j : M ↪ N\` gives a complete filling
\`j[X] : M[X] ↪ N[X]\`. The designated targets are the **labelled
pairs (j,s)**. Their sibling choices under the same j are disjoint;
different old parents j may overlap. **Never delete** unselected
ambient N or N[X] edges.

The exact physical colouring calculation is:
\`χ(ι_{j[fₛₚ]}[sₚ(e)]) = χ_{j[fₛₚ]}(sₚ(e)) = ρ(sₚ(e)) = c\`
for every original target edge e, with ONE old parent j, ONE selected
W-copy s and the SAME complete word ρ across every first wagon.
The final conclusion must be about the actual designated family,
not merely an arbitrary monochromatic edge subset.

## Reused existing Lean (do not re-prove)

- \`TrainFillingTemplateConstruction\`: canonical physical edge
  equivalence, unique old cover and generated-edge linearity.
- \`TrainFillingPrivateExtension\`: exact private-vertex intersections,
  original target containment and local scattering geometry.
- \`TrainFillingIndexedActualMPhysicalTrain\`: actual contracted
  M-support-to-physical-edge equivalence and faithful train cuts,
  **conditional on the specific support equality**.
- \`TrainFillingIndexedSelectedPhysicalMap\`: full physical
  heterogeneous G0-to-H edge embedding and range, no pruning.
- \`TrainFillingIndexedMonotoneCarrierBridge\`: finite uniqueness
  of increasing coordinate placements, yielding all filled-edge
  carrier equalities from full old carrier equality.
- \`TrainRecursiveWitnessPass\` and
  \`TrainFillingSelectedStageTrainReflection\`: actual selected
  shorter-stage M-copies, their physical old A-edge maps and
  preservation **and reflection** at every train cut.
- \`TrainFillingOrderStageCanonicalAllCutGirth\`: for the actual
  **OrderStage**, all proper old cuts have full system-girth
  bounds, INCLUDING the old equality cut. Use its canonical
  filling theorem, not the weaker bare ForestTailStage tail bounds.
- \`TrainFillingIndexedParentwiseRealization\`,
  \`TrainFillingIndexedFaithfulParentwise\` and
  \`TrainDesignatedSubcopyGirth\`: global scattering preserving
  ALL ambient edges, no cross-parent disjointness assumption.
- \`TrainFillingIndexedSelectedColourWord\`: literal two-arrow
  filled edge-colour identity; used with the true selected b below.

Prior Lean verification of these older modules is **not** a
certificate for any candidate added in this PR.

## New *candidate*, uncompiled bridges in PR #1063

1. **Unequal first wagons:** \`PrivateSummand\`,
   \`PrivateSelectedUnion\`, \`PrivateSelectedColour\`,
   \`PrivateSelectedFamily\`, \`PrivateSelectedIndexedArrow\` and
   \`PrivateEHNArrow\`. These construct local private embeddings of
   different types \`Fₚ\` from ONE selected \`s(W)\`, derive
   A-strongness by composition, supply complete common X support,
   and derive the exact local \`selectedCommonEdges\` Ramsey arrow
   from the genuine EHN closed-target arrow. The real assumptions
   \`A ↪ W\` nonempty and local vertex coverage remain visible.

2. **Genuine lower selected parent:** \`PrivateStageSelectedPhysical\`,
   \`PrivateSelectedStageFilling\`, \`PrivateSelectedOldRange\` and
   \`PrivateActualOrderParent\`. They construct βⱼ from the selected
   \`OrderStage\` copy **j itself**, rather than postulating a new
   injection. The full old-edge image is exactly the ambient A-support
   edges contained in j(M), and all proper-cut relations are
   preserved/reflected through that SAME βⱼ.

3. **Actual filling and scattering:** \`PrivateCanonicalParentwise\`,
   \`PrivateCanonicalCutBridge\`,
   \`PrivateActualOrderRealization\` and
   \`PrivateActualOrderStrictMono\`. These construct the actual
   parentwise vertex/edge maps, full copy-edge range and quotient
   wagon maps for **all** selected j, then identify the resulting
   incidence data with the canonical inherited cut. The primary
   interface uses exact *edge carrier images*, not arbitrary
   separately assumed output wagon maps or pointwise coordinates.
   The new strictMono theorem derives the carrier images from full
   first-wagon carriers plus source, selected-copy and canonical
   placement order compatibility. The new
   \`canonicalFilledSelected_targetFullSystemGirthGT_of_inherited_carrier\`
   transfers the old full bound to the same target family without
   assuming output girth.

4. **The true labelled arrow:** \`PrivateActualWordArrow\` first
   pulls a full old N-edge colour word back to actual A-embeddings,
   then returns the genuine selected j (not just an abstract β).
   Its source A-copy is derived from a nonempty index
   \`C × P\`; it is not an unrelated default-colour assumption.
   \`PrivateActualIndexedArrow\`,
   \`PrivateParentwiseColour\` and
   \`PrivateActualLabelledArrow\` combine that selected j with
   the ONE EHN s to obtain monochromaticity on the *actual*
   \`designatedFamily.target.copyEdges (j,s)\`.

5. **Exact-head check gate:** \`Girth/CheckTrack5Private.lean\`
   contains targeted \`#check\` and \`#print axioms\` probes. It
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
\`ab, ac, bd, cd\` is linear, but first wagons
\`F₀={ab,ac}\` and \`F₁={bd,cd}\` share both b and c.
Private contraction would therefore have two old common vertices,
contradicting linearity. The actual cutoff-two assumption
\`girth(W₁(T)) > h₁ ≥ 2\` forbids this labelled two-cycle.
The manuscript preliminary lemma now *states* the required first
wagon carrier linearity and the application *derives* it. It
also explicitly requires ≥2 vertices in each template X-edge
for uniqueness of the old cover (automatic for the coloured
edge type under discussion).

The common-edge arrow was fixed after discovering an incorrect
attempt to treat a transported \`CommonTemplateEdge\` as a member
of the original local selected-edge subtype. The proof now uses
the actual local selected element first and transports it
through \`choiceTemplateEquiv\`.

The manuscript had a literal \`\\nFor\` inside the canonical
filling statement; that TeX command was corrected to a real
newline. The disjoint union M now explicitly tags every
vertex by s, including old target vertices.

## Executed bounded regression (NOT a general formal proof)

Local \`/mnt/data/track5_private_smoke.py\` ran successfully:
- Two unequal Fₚ: three versus four original vertices.
- Disjoint-union W: seven vertices and five original edges.
- Two selected X-copies: fourteen template vertices, ten template
  edges, four contracted first-wagon edges, forty filled edges.
- Two selected old parent copies whose images SHARE one vertex;
  the FULL ambient N has eight old edges and its filling has
  **80 physically distinct edges**, retaining all unselected edges.
- All four labelled \`(parent,choice)\` target edge families retain
  their original edges, are strongly induced and satisfy the
  appropriate complete colour-word calculation. Sibling choices
  remain disjoint, while cross-parent overlap is allowed.
- The four-edge first-wagon-carrier counterexample is reproduced.

This is a finite sanity check, NOT an EHN theorem, Ramsey arrow
for arbitrary colourings, Lean verification or proof of general
full system girth.

## What actually remains to close \`lem:tailraw\`

1. Instantiate the **ordered, partite**, actual colour-block
   relational M of the selected unequal-summand family.
   Discharge all \`hColour\`, \`hCoordinate\`, \`hXBlocks\`,
   \`hSupport\`, old-carrier linearity and target order hypotheses
   of the existing actual M-support and ordered-carrier lemmas.
2. Supply the genuine shorter \`RR_h\` witness as the required
   *selected* \`OrderStage\` with its \`DesignatedArrow\` and
   \`allCutGirth\`. The abstract formal OrderStage alone does
   not assert global \`StrictMono\` for every selected embedding;
   establish that from the actual block-ordered colour language,
   or choose the correct ordered presentation instead of assuming it.
3. Identify the ONE canonical full support filling N[X] and its
   inherited train with the concrete \`OrderStage\` input at each
   old cut. Apply \`OrderStage.canonicalFilledCut_fullSystemGirthGT\`
   and the carrier-only parentwise/scattering lemmas, **not** a
   new or circular output-girth assumption.
4. Identify each selected \`(j,s)\` target with an actual copy of
   the ORIGINAL T, preserving every part, order and train relation.
   The candidate labelled monochromaticity lemma establishes
   only the edge-colour part until this is done.
5. Perform a local *exact-head* Lean build, then inspect
   \`#print axioms\`, hidden universes and every proof hypothesis.
   Build the full TeX to certify all source changes. This container
   has no Lean/lake/elan binary, its git process cannot resolve
   github.com, and the 2026-11-08 prebuilt Lean/mathlib bundles are
   not mounted. We have **not run** a kernel check or paid GitHub
   Actions. The PRs must stay **draft and unmerged**.

**No new validation mark is justified.** This is an adversarial
source audit and an explicit, testable integration plan.
