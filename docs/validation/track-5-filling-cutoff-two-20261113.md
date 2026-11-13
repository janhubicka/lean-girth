# Track 5: direct cutoff-two filling — statement and interface audit

Date: 2026-11-13. Work queue: [#1056](https://github.com/janhubicka/lean-girth/issues/1056).
Numbered programme: [#1060](https://github.com/janhubicka/lean-girth/issues/1060).

## Exact target and safety boundary

- Base manuscript: \`janhubicka/girth/main@8c9cfa6eb6d817a08f3009fe048fc0be07426ece\`, 41-page revision, baseline reachable-source digest
  \`45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec\`.
- Base Lean: \`janhubicka/lean-girth/main@98e40142f95cf818f498ed21faf9302a50fe7832\`, with historic checked proof library based on \`e57c954c6417604d35332adfdf3304a225281eca\`.
- Manuscript draft branch: \`revision/track5-private-summands-20261113\`.
- Lean draft branch: \`validation/5-filling-cutoff-two\`.
- Neither branch changes a completed validation mark to green. No new Lean kernel check or TeX compilation is claimed; no paid Actions requested. The manuscript **branch** has different sources from the pinned **main** digest.

## Manuscript target and old reusable endpoints

| Manuscript assertion | Reusable Lean declaration / boundary | Current status |
| --- | --- | --- |
| \`obs:canonicalfilling\` — canonical filling, exact edge pairs, inherited parameters, selected train embedding | \`UniformFillingData.toTrainFilling\`, \`edgeEquiv\`, \`generated_linear\`; \`TrainFilling.inheritedTrain_adjacentParameters\` and inherited wagon maps | Reusable components. Complete selected-copy adapter is **open**. |
| \`thm:derivation\` — full system-girth preservation through filling | \`TrainFilling.filled_fullSystemGirthGT\` in \`Girth/TrainFillingSystemGirth.lean\` | Historical proved transfer. Actual application needs old full bound and generated-edge linearity; neither output girth nor edge deletion may be assumed. |
| \`thm:scattering\` — designated-subcopy restriction | \`OrderOneData.DesignatedSubcopyFamily.fullSystemGirthGT_of_components\` in \`Girth/TrainDesignatedSubcopyGirth.lean\` | Historical proved transfer. Requires concrete full parentwise realization and local target geometry. |
| \`lem:privateextension\` — different first-wagon summands | \`PrivateWagonInput.range_inter\`, \`PrivateWagonInput.componentGeometry\`, indexed private labelled-girth and cut-parameter adapters | New English preparatory lemma and candidate unequal-summand Lean adapter; complete kernel check **open**. |
| \`lem:tailraw\` — direct cutoff-two Ramsey witness, indexed target and arrow | \`IndexedPrivateChoice.selectedIndexedFilledEdgeEmbedding\`, \`selectedIndexedTargetEdges_ramsey_of_two_arrows\`, \`selectedActualMPhysicalEdgeEmbedding_train_iff\`, \`IndexedPrivateChoice.ParentwiseRealization.target_fullSystemGirthGT\` | Conditional pieces exist, but no constructed final indexed \`(j,s)\` witness, nor a proof of exact all-level actual parentwise realization. Remains **open**. |

## Substantial application gap found

The literal English argument sets \`W = disjoint union_p F_p\` and
\`s_p = s ∘ u_p : F_p -> X\`. It does **not** identify each \`F_p\` with
the entire \`W\`. The previous special-purpose constructor
\`UniformPrivateTemplate.toPrivateWagonInput\` and the EHN indexed
constructor in \`TrainFillingRamseyIndexedChoices.lean\` instead require
\`identify : forall p, oldCarrier(p) ≃ W\`, which can fail even by
cardinality. Using them without a new adapter would silently change
the statement.

Two new candidate modules repair this *interface*, without claiming
to finish the cutoff-two theorem:

1. \`TrainFillingPrivateSummand.lean\`:
   \`SummandPrivateTemplate.toPrivateWagonInput\` constructs the
   \`PrivateWagonInput\` for unequal \`F_p\` from each summand's genuine
   local strong embedding and individual selected edges, while keeping
   the same complete template-edge family of \`X\`.
2. \`TrainFillingPrivateSelectedUnion.lean\`:
   \`aStrong_compose\` proves transitivity of strong inducedness via
   factorization of A-copies through the selected image;
   \`SummandPrivateTemplate.fromSelectedUnion\` builds all summand
   templates from one and the same \`s : W -> X\` and the actual
   inclusions \`u_p : F_p -> W\`, assuming each \`u_p\` is A-strong
   (to be derived from the explicit disjoint union) and each
   \`F_p\` is A-covered.

**Proof of the new transitivity statement (paper-level):**
If an A-copy \`a\` in \`X\` meets \`s(u(F))\` in at least two points,
it also meets \`s(W)\` twice. Strongness of \`s\` forces \`a\`
inside \`s(W)\`; factor \`a=s∘b\` through \`s\`. Injectivity of \`s\`
gives two points of \`b\` in \`u(F)\`; strongness of \`u\` forces
\`b\` into \`u(F)\`, hence \`a\` into \`s(u(F))\`. This is not a
new hypothesis of output strongness.

The new English preparation lemma spells out actual first-wagon
intersection equalities, transported ordered edge types,
proper-cut labelled girth, strong embedding \`T -> M_s[X]\`, and both
local scattering conditions. Section 16 now uses it in place of
repeating all these facts inside the Ramsey argument.

## Adversarial checks and remaining obligations

1. **No assumption of first-wagon equipotence.** Every source summand has
   its own type, inclusion and coordinate; a *single* \`s(W)\` must be
   used across all summands for colour uniformity.
2. **Exact physical label indices.** Use the complete pairs
   \`(old edge f, local X-edge e)\`, not a carrier quotient with lost
   occurrences. Restricting a selected copy is not deleting ambient
   filled edges.
3. **Old-parent index first.** Target labels are \`(selected j, choice s)\`;
   the \`s\` components are disjoint only for the *same j*. Different
   selected \`j\` may overlap.
4. **Shared universal top.** Do not demand a girth bound or proper
   wagon separation at the universal top.
5. **Nontrivial template edges and linear first-wagon carriers.**
   The proof uses the unique old cover of each filled edge, which
   requires each \`X\`-edge to have at least two vertices. Separately,
   *linearity of T's underlying edges does not imply linearity of its
   first-wagon carriers*: two distinct first wagons can share two
   vertices via different original edges. The new preparation lemma
   therefore explicitly assumes linearity of \`W_1(T)\`. This holds in
   \`lem:tailraw\` because the first tail wagon-girth bound is
   \`>h_1>=2\`; without it the shortened train M need not be linear.
6. **Construct, don't assume, final realization.** Need to derive
   the \`ParentwiseRealization\` vertex map, complete physical edge
   map, exact carriers, copy ranges and proper wagon parent map from
   an actual selected \`M\`-copy \`j\`. The existing faithfully
   indexed adapter \`FaithfulParentwisePhysicalRealization\` still
   asks for actual carrier and edge-parent identities.
7. **No circular girth.** Derive old \`N\` full system girth from
   \`RR_h\`, use actual generated-edge linearity, then call
   \`filled_fullSystemGirthGT\`, then scattering; do not postulate
   output bound.
8. **Exact indexed arrow.** Colour each \`N\` edge by its *entire*
   function \`E(X)->r\`. First select one \`j(M)\` carrying a common
   colour-word \`rho\`, then choose one \`s(W)\` monochromatic under
   that same \`rho\`. Transport physical edges via
   \`iota_{j[f]}[e] = j[iota_f[e]]\`. The abstract colour-word lemma
   does not by itself construct the final embedding.
9. **Order and parts.** Need the actual coloured-edge enumeration,
   global within-part order extension, all shifted \`A_2,...\`
   parameter identities, and selected-copy reflection at every
   proper cut. Reuse the existing indexed ordered-placement and
   actual-selected-train modules.
10. **Build obligations.** Run local \`lake env lean\` on both new
    files, exact-head dependency build, source scans for \`sorryAx\`
    and \`#print axioms\` for the exported declarations. These steps
    have **not** been executed on this branch.

## Next minimal integration goal

Compose the specific \`SummandPrivateTemplate.fromSelectedUnion\`
with the EHN witness of the disjoint union (without requiring
\`F_p ≃ W\`), then the checked actual contracted-\`M\` equivalence,
and finally construct \`FaithfulParentwisePhysicalRealization\` for
every selected \`j\`. Only after this yields the actual \`(j,s)\`
arrow, the exact indexed girth bound, and a local Lean build/axiom
audit can \`lem:tailraw\` receive a verified marker.


## Continuation: one EHN selected union supplies the local indexed arrow

Additional candidate files on the SAME Track 5 branch (not kernel checked):

- \`Girth/TrainFillingPrivateSelectedColour.lean\`:
  \`selectedUnion_summand_monochromatic\` and
  \`SummandPrivateTemplate.selectedEdges_monochromatic_of_selectedUnion\`.
  These show a physical A-support edge in any individual first-wagon
  summand is monochromatic whenever the *one enclosing selected W-copy*
  is monochromatic, without choosing separately for different p.
- \`Girth/TrainFillingPrivateSelectedFamily.lean\`:
  \`selectedUnionPrivateChoices\` builds the entire choice-indexed
  heterogeneous G0 family \`C -> PrivateWagonInput\` from one
  selected W-embedding per c, with literal same template-edge family.
  \`selectedUnionPrivateChoices_localArrow\` transports a global W-arrow
  into uniform local monochromaticity for all first wagons.
- \`Girth/TrainFillingPrivateSelectedIndexedArrow.lean\`:
  \`selectedUnionPrivateChoices_commonLocalArrow\` converts the local
  result through \`choiceTemplateEquiv\` to the exact
  \`selectedCommonEdges\` type of \`selectedIndexedTargetEdges_ramsey_of_two_arrows\`.
- \`Girth/TrainFillingPrivateEHNArrow.lean\`:
  \`closedTargetRamseyFamily_supportArrow\` pulls a physical-edge-word
  colouring back along actual A-embeddings of X, invokes the genuine
  closed-target Ramsey arrow, and chooses its common colour from a
  specified nonempty A-copy of W.
  \`exists_colouredRamsey_unequalSummandPrivateChoices\` packages the EHN
  witness, all selected closed W-copies, their A-strong composed summands,
  common template support family and exact \`selectedCommonEdges\` arrow.

**Referee point:** These declarations are candidate English-to-Lean adapters,
NOT a kernel-verified Ramsey theorem. They still take the finite ordered
A-linear W and actual relational component embeddings \`F_p -> W\` as
data; constructing this disjoint-union W and showing the inclusions
A-strong and each component A-covered remain source application
obligations. The \`Nonempty (Embedding A W)\` hypothesis in the
supportArrow is real: a monochromatic *colour* cannot be extracted
from an empty selected A-edge family without a default \`κ\` element.
Here it follows from the nonempty edge type and nonempty first wagons;
it has not been silently erased.

After this local EHN portion, the **hard gap** is no longer an
independent colour choice in each F_p, but the genuine selected
shorter-stage \`M -> N\` strong train embedding with exact canonical
X-placements, and a \`FaithfulParentwisePhysicalRealization\` for
every selected old parent. This is needed to convert the already
available physical two-arrow colour calculation into the final
\`(j,s)\`-indexed Ramsey witness and full tail system girth.

**Build constraint in this session:** the runtime has no Lean/lake
binary, cannot resolve github.com from its container, and none of
the large precompiled Lean/mathlib archive ZIPs is mounted. Old
GitHub CI successes certify older exact heads only. As instructed,
no paid Actions have been triggered. All new declarations retain
unverified status until a local exact-head compilation and
\`#print axioms\` audit can be performed.


## Continuation: actual shorter-stage physical copy and restored wagons

The next candidate chain reuses the EXISTING selected \`ForestTailStage\`,
rather than introducing an independent selected embedding \`M -> N\`:

- \`TrainFillingPrivateStageSelectedPhysical.lean\` derives a
  **single** physical edge injection from a genuine selected lower-stage
  copy \`b\`, with exact complete first-wagon carriers and faithful
  equivalence for **every** train cut. It packages
  \`selectedActualMPhysicalEdgeEmbedding\` and
  \`selectedActualMPhysicalEdgeEmbedding_train_iff\`.
- \`TrainFillingPrivateSelectedStageFilling.lean\` transports the
  actual filled old-edge type (which must equal the **full**
  A-support of \`S.system.toRelStructure\`) to the lower-stage
  physical support edges. It constructs the canonical selected
  \`(choice,first-wagon) -> H.OldEdge\` map from the genuine selected
  relational \`b\`, proves exact complete carrier images, defines
  the corresponding H-old train by an edge equivalence and derives
  every-cut faithfulness from the stage's *actual*
  \`targetRestriction\`. No independent β/hFaithful input.
- \`TrainFillingPrivateSelectedRestoredWagons.lean\` instantiates
  the existing \`selectedIndexedRestoredWagonEmbedding\` with that
  **actual** β and transported old train. This constructs one
  injective positive-cut proper-wagon map and its exact physical
  parent equation, under genuine source quotient and local template
  nonemptiness. It correctly does **not** treat the shared universal
  top as a proper cut.

An exact-head gate is included in \`Girth/CheckTrack5Private.lean\`.
It imports both the EHN and stage branches and includes targeted
\`#check\` and \`#print axioms\` probes. This file has **not** been
executed: presence of a probe is not kernel validation.

**Remaining genuinely hard application obligations** (do not silently
promote):

1. Show the concrete contracted colour-block relational \`M\`
   from the selected EHN family has precisely the original
   \`(choice,first-wagon)\` complete A-support carriers. The older
   indexed actual-M support theorem is reusable, but its hypotheses
   must be discharged from the new unequal-summand model.
2. Obtain the actual selected shorter \`ForestTailStage\` from
   \`RR_h\` and transport its partite predicates and orders through
   the canonical placements. For each selected old parent \`b\`,
   establish pointwise canonical-placement compatibility
   \`H.place (β_b (c,p)) x = b(tagVertex c (U_c.place p x))\`,
   or derive the corresponding **complete** physical carrier identity
   from ordered carrier uniqueness as in the older adapter.
3. Construct a \`FaithfulParentwisePhysicalRealization\` into
   the unchanged full \`H=N[X]\`. The selected β, all-cut
   parent reflection and proper-wagon embeddings are now supplied
   by the candidate chain; the vertex map, physical carrier
   equality, selected parent \`copyCarrier\`/\`copyEdges\` and final
   target indexed by \`(b,c)\` still require exact assembly.
4. Prove the old \`N\` full system-girth input at each cut used
   for the filling theorem **without** invoking the desired output
   girth. The lower-stage stage supplies only its stated tail
   coordinates; do not invent a missing bottom system bound.
5. Combine the actual selected parentwise family with the
   already-available indexed EHN local arrow and selected physical
   colour-word theorem. Only then may \`lem:tailraw\` be closed.

**Adversarial source check (not Lean elaboration):** ten new Lean
files on this branch (including the check gate) were inspected for
balanced braces, balanced namespace declarations, dependencies,
and forbidden top-level \`sorry\`, \`admit\` or \`axiom\` declarations;
a missing final EHN namespace terminator was corrected in a
follow-up commit. The TeX draft retains open/partial markers.
No successful Lean or full PDF build is being represented by this check.
