# Track 5 — current cutoff-two validation map (16 November 2026)

**Scope:** `paper/13-filling.tex` and `paper/16-cutoff-two.tex`;
numbered [issue #1056](https://github.com/janhubicka/lean-girth/issues/1056).
This is the girth-5 programme's **numbered Track 5**, not a
legacy lettered track.

**Source branches:** [Lean draft PR #1063](https://github.com/janhubicka/lean-girth/pull/1063)
(`validation/5-filling-cutoff-two`) and
[manuscript draft PR #450](https://github.com/janhubicka/girth/pull/450)
(`revision/track5-private-summands-20261113`).
Source base: girth `8c9cfa6e`, lean-girth `98e40142`.
Both PRs intentionally remain **draft and unmerged**.

> **Verification boundary.** The new Track 5 declarations below are
> source-level *candidates*. No new Lean module was compiled on its exact
> head, and no `#print axioms` output has been inspected. Earlier checked
> imports do NOT certify new applications. No green marks, no paid CI,
> and no full TeX build are claimed.

## Critical correction — raw versus COMPLETED ordered W

The direct EHN source of the manuscript is the **ordered disjoint
union** of the first wagons. The existing
`PrivateRealDisjointUnion` and
`PrivateRealColouredEHN` candidate files construct a RAW
relational coproduct: every relation tuple, INCLUDING the binary
within-colour order relation, belongs to one summand.
A separately declared auxiliary `LinearOrder` on that vertex
type **does not insert the missing binary relational pairs**.

If distinct first wagons contain vertices of the same predicate
colour, raw W cannot embed inducedly into a fully ordered coloured
hypergraph X: any two images have a comparison in X in one direction
which is absent from raw W in BOTH directions. This is a REAL
interface obstruction, not an open proof of an obviously
automatic equivalence.

**Executed finite counterexample** (16 November):
`/mnt/data/track5_order_completion_obstruction.py`
has two disjoint 2-edge wagons with four same-colour vertices.
Exactly **0/24** bijections from raw W into a fully ordered
coloured X are induced order embeddings; after completing W's
binary within-colour order, there is **1/24**.
Different-colour summands yield no cross-colour obstruction.
This is a finite counterexample to an invalid shortcut, not
a counterexample to the Ramsey theorem.

**Corrected manuscript PR #450:** form W with the componentwise
**hyperedge** relation but add comparisons between all
same-colour vertices according to a global order extending
each summand's order. Every coloured edge remains inside a
summand because its full k-ary edge relation was not changed.
The EHN-to-coloured-X completion is part of Track 1's
`lem:unrestricted`, not a trivial consequence of a raw
`ElementaryCAClass` reduct.

**New candidate source**:
- `PrivateRawOrderObstruction` records absence of
  cross-summand order and the no-induced-embedding obstruction;
- `PrivateCompletedOrderedW` defines the correct
  completed relational W, preserves componentwise edge
  membership and supplies the completed order relation;
- `CheckTrack5RawOrderObstruction` isolates their
  `#check` / `#print axioms` gates.

**Not yet proved in Lean:** each F_p remains a full induced
relational substructure of the completed W; completed-W
A-linearity/coverage/monotonicity; replacement of RAW-W in the
ordered EHN selected-family arrow; and the marked, covered
X output. The RAW-EHN lemmas remain preparatory, **not a
proof of the completed ordered first Ramsey input**.
Do not promote their associated validation markers.

The earlier offline Lean setup guide was found in the
Library. It pins the same `v4.35.0-rc3` compiler, but the
old successful Ubuntu bundle from 8 November currently
exposes **zero available workflow artifacts**. The
container has no installed compiler/mathlib workspace.
No exact-head kernel/axiom check could be run in this turn.

## Critical correction — TWO edge types in the filled OrderStage

A new adversarial audit detected that
`TrainFillingOrderStageCanonicalAllCutGirth.lean` proves its
`OrderStage.canonicalFilledCut_fullSystemGirthGT` statement
using the **same source coloured edge type A** for both
old selected edges of N and local inserted edges of X.
This is NOT the actual cutoff-two situation:

- The shorter `RR_h` old edge type `A_old` has the entire
  ordered coloured vertex set `V(X)` as its vertex set.
- The inserted hypergraph X carries edges of the original,
  typically SMALLER `A_small = E_a` edge type.

These can have different cardinalities AND different
relational languages. No `A_old → X` embedding is
required or generally available. The previously listed
one-type OrderStage theorem is **not** a direct
certificate for cutoff two.

New candidate `Girth/TrainFillingPrivateTwoTypeOrderGirth.lean`
proves an explicit **two-relational-language** generalization:
construct `H := UniformFillingData.ofSupportCopies A_small X
  (supportCopies A_old N) place ...`, then apply the
ALREADY CHECKED generic
`H.toTrainFilling.inheritedCutData_fullSystemGirthGT_of_fibreLinearity`
with:

1. the actual shorter `OrderStage.allCutGirth j` of
   the *old* large-edge type;
2. `S.aLinear` to make all old N-support edges linear;
3. `A_small`-linearity to make local X-fibres linear; and
4. full X-coverage by its *small* A-support edges.

The result is full inherited system girth for each old cut
(including equality zero), with the actual selected old
parent/copy-edge family, **without** identifying the two
edge types or assuming output girth.
This candidate is uncompiled: its new
`#check`/`#print axioms` gate has not been executed.

Two further **uncompiled candidate** modules now make
that same-H identification explicit:

- `Girth/TrainFillingPrivateCanonicalTwoTypeOldTrain.lean`
  proves the canonical H old-edge equivalence is
  the identity and the transported selected old
  train is exactly `S.train`.
- `Girth/TrainFillingPrivateActualTwoTypeTargetGirth.lean`
  composes that identity with the two-type OrderStage
  bound, the actual selected parent and old edge range,
  ordered carrier uniqueness, and generic global
  scattering. It aims to derive the FULL labelled
  `(j,s)` target system girth without asking for
  output girth.

`Girth/CheckTrack5TwoTypeGirth.lean` is an isolated
kernel/axiom gate importing ONLY the foundational
two-type theorem and checked dependencies. Its
commands have NOT been executed.

**Remaining validation:** actual `RR_h`/EHN integration,
kernel compilation of each new lemma (especially
the same-H identity and combined scattering statement),
and a manual full-paper TeX build. The old one-type
theorem is still useful in its own setting but must
not be cited as closing this two-type proof.

## Mathematical chain

Given the original height-\(1+m\) train \(T\), denote its **actual**
first-wagon edge quotient by \(P=E(T)/{\sim_1}\), and the wagon
carriers by \(F_p\). The old tail bound \(>h_1\ge2\) gives *labelled*
first-wagon carrier linearity; ordinary linearity of the individual
old edges **does not** imply this condition.

1. **The first EHN target is \(W=\coprod_{p\in P}F_p\).**
   First wagons may have different cardinalities and structure types.
   Their disjoint union uses tagged vertices, but each selected
   \(W\hookrightarrow X\) is ONE copy; its restrictions \(s_p\) are
   not independently selected.

2. **Private contraction.** The selected \(s_p\) identifies original
   \(F_p\) vertices with their \(X\)-coordinates. Other coordinates
   are private to that first wagon, yielding one edge \(f_{s,p}\)
   with full coordinate set \(V(X)\).
   Build \(M_s\) on those edges, then build the disjoint
   choice union \(M=\coprod_s M_s\). Only the top wagon is shared.

3. **One shorter Ramsey selection.** Apply the
   **unrestricted ordered** \(\mathsf{RR}_{\mathbf h}\) to \(M\),
   colouring each old edge by its **entire**
   function \(E(X)\to r\). Although every edge has
   coloured type \(V(X)\), \(M\) need **not** be partite
   over individual \(X\)-positions: shared old vertices can
   occupy different positions in different first wagons.
   Their unary predicate colours agree, which is enough
   for the ordered assertion. The selected old parent
   is a genuine \(j:M\hookrightarrow N\).

4. **Canonical full filling.** Use \(H=N[X]\) without deleting
   any ambient edges. Let \(\tau_s:V(T)\to V(M)\)
   include old vertices into the *tagged* \(s\)-component.
   For an original \(e\in F_p\), the correct physical formula is
   \[
     \iota_{j[\bar f_{s,p}]}[s_p(e)]
        =j[\alpha_s[\beta_{s,p}[s_p(e)]]]
        =j[\tau_s(e)].
   \]
   The old incorrect expression `j[e]` was ill-typed.

5. **Labelled targets and cuts.** Keep the genuine selected
   pair \((j,s)\), preserving the original edge/vertex
   images and every train relation. Different choices in one
   selected parent are disjoint; DIFFERENT old parents may overlap.
   At the bottom distinct original edges remain distinct;
   positive levels shift by one, and the universal top is shared.

6. **Both arrows.** All old edges of \(j(M)\) have one common
   complete colour word \(\rho\). Apply the first EHN arrow to
   that SAME \(\rho\), choosing ONE \(s(W)\).
   Every original edge in its \((j,s)\)-labelled copy has the
   same \(\chi\)-colour. Retain one representative per image if
   duplicate designated target labels occur.

7. **Full system girth.** The shorter \(\mathsf{RR}_{\mathbf h}\)
   yields an actual `OrderStage`, with all-cut system girth
   including its old equality cut. First apply canonical filling
   to that FULL ambient system, then the checked
   global designated-subcopy scattering theorem to the selected
   \((j,s)\) targets. Do not assume the desired output girth.

## Reused older modules

The repository already contains generic proofs which should **not**
be duplicated in the final cutoff-two assembly:

- `TrainFillingPrivateExtension`: old/private geometry and
  component-local coverage/strongness conditions.
- `TrainFillingTemplateConstruction` and
  `TrainFillingSelectedEdgeRange`: canonical full-X edge
  equivalence, old covers and full edge-image ranges.
- `TrainFillingIndexedMonotoneCarrierBridge`: unique
  increasing placements from complete first-wagon carriers.
- `TrainFillingIndexedContractedTrainGirth` and
  `TrainFillingIndexedPrivateParentParameters`: dependent
  tagged/private girth and allowed-part transfers.
- `TrainRecursiveWitnessPass` and
  `TrainFillingSelectedStageTrainReflection`: genuine selected
  shorter-stage parent and all-cut train reflection.
- `TrainFillingOrderStageCanonicalAllCutGirth`: one-type
  old all-cut filling transfer (not directly the large/small cutoff-two instance).
- `TrainFillingPrivateTwoTypeOrderGirth`: **new uncompiled** two-type
  adapter to the checked generic `inheritedCutData_fullSystemGirthGT_of_fibreLinearity`.
- `TrainFillingIndexedFaithfulParentwise`,
  `TrainDesignatedSubcopyGirth` and
  `TrainDesignatedSubcopyStrong`: exact global scattering,
  target strongness and girth, with full ambient edges.
- `TrainFillingIndexedSelectedColourWord`: literal physical
  two-arrow monochromaticity transport.

These are reusable interfaces, **not** a blanket verification
claim for the new Track 5 constructors.

## New candidate proof modules, grouped by purpose

### A. Original \(T\), first wagons, and the EHN source \(W\)

- `PrivateActualWagonOwner` and
  `PrivateActualFirstWagonSource`: first-wagon owner is its true
  `EdgeTrainLevels.wagonSetoid 1` class; wagon carrier is the
  union of complete owned edges; original labelled girth \(>h_1\)
  gives carrier linearity, not merely ordinary edge linearity.
- `PrivateFirstWagonStrong` and
  `PrivateActualSourceEdgeEquiv`: an induced first wagon cannot
  acquire a foreign edge, and
  \[
       E(T)\cong\coprod_p E(F_p)
  \]
  as **physical support-edge labels**. The first-wagon
  owner map is constructed from the original quotient, not assumed.
- `PrivateRealDisjointUnion`, `PrivateRealUnionOrder`,
  `PrivateRealUnionLinear` and `PrivateRealUnionColoured`:
  the RAW dependent tagged coproduct and a SEPARATE
  auxiliary colour-first order. These are useful
  free-amalgamation preparations, but the binary within-colour
  relations of raw W do not compare different summands.
  `PrivateCompletedOrderedW` now defines the intended
  relational order completion. Its exact EHN interface
  and induced summand properties are OPEN.
- `PrivateRealUnionColouredMono`,
  `PrivateRealUnionLocalCoverage`,
  `PrivateRealUnionEHN`, `PrivateRealColouredEHN`,
  `PrivateActualWagonEHN`: derive the ordered EHN
  source geometry for the RAW relational W from original
  \(T\). This is **not yet** the completed ordered
  W needed by `lem:unrestricted`. There is no
  requirement \(F_p\simeq W\).

### B. Ordered EHN selections and the actual shortened \(M\)

- `PrivateSummand`, `PrivateSelectedUnion`,
  `PrivateSelectedFamily`, `PrivateSelectedColour`,
  `PrivateSelectedIndexedArrow`: construct individual
  heterogeneous private inputs from ONE selected \(W\)-copy and
  derive the SAME local selected-edge colour for all \(p\).
- `PrivateMonotoneEHN`, `PrivateMonotoneSummands`,
  `PrivateMonotoneExistence`: retain genuinely **increasing**
  EHN selected embeddings. The ordinary `ClosedTargetRamseyFamily`
  forgets their order, so using all closure embeddings as
  choices would be incorrect.
- `PrivateColourBlockOrder` and
  `PrivateColourCompatibility`: sort \(X\) into predicate
  blocks without changing the selected original EHN-choice
  index set. The lemma
  `monotoneSelectedUnion_coordinate_mono_reblocked` explicitly
  transports its *old-order* monotonicity certificates.
  Correct universe parameters are retained.
- `PrivateReblockedContractedM` and
  `PrivateReblockedEnumeration`: derive the actual
  coloured `M` support and the required increasing
  finite enumeration from unary colours and the chosen orders.
- `PrivateCoveredEHN`: original \(W\) copies survive
  restriction to the A-supported vertices of \(X\);
  the **full ordered/marked Ramsey arrow after restriction
  is not yet proved here**, and belongs to Track 1.

### C. Genuine quotient-tail train and its parameters

- `PrivateActualTailQuotient`: the shortened edge train
  is `T.tailQuotient` on old first-wagon quotient labels.
  At shortened level \(\nu\), equality/reflection is
  exactly old relation \(\nu+1\).
- `PrivateTailWagonEquiv`: a true quotient-of-quotient
  equivalence of ALL wagon labels at each shifted cut,
  with exact vertex carriers, commuting parent maps,
  bidirectional **labelled** girth transfer and
  allowed-part intersection transfer.
- `PrivateActualTailParameters`: the existing
  `PrivateWagonInput.expandedWagonClass_parentBound`
  transfers those source parameters through the actual
  private vertices; no independently assumed shortened
  parameter bound.
- `PrivateActualChoiceTrain`: inside a single EHN choice,
  the contracted train is exactly the old shifted
  original train; different choices are separate at all
  proper cuts, and the top is one global wagon.

### D. Selected \(M\)-copy, actual filled \(H\), and target \(T\)

- `PrivateStageSelectedPhysical`,
  `PrivateSelectedStageFilling`,
  `PrivateSelectedOldRange`,
  `PrivateActualOrderParent`: from the **actual**
  selected `OrderStage` copy \(j\), construct the
  complete original first-wagon edge map into the full
  \(N\)-support and reflect all shortened train levels.
- `PrivateCanonicalParentwise`,
  `PrivateActualOrderRealization`,
  `PrivateActualOrderStrictMono`,
  `PrivateCanonicalCutBridge`: construct the real
  selected parentwise maps using **exact edge carriers**;
  compare the same complete \(H\) cut with
  `inheritedCutData`. The checked all-cut girth theorem
  can then feed global scattering.
- `PrivateActualWordArrow`,
  `PrivateActualIndexedArrow`,
  `PrivateActualLabelledArrow`,
  `PrivateParentwiseColour`: preserve the SAME selected
  old \(j\) and EHN \(s\) through the full colour-word arrow
  to the labelled designated target edge family.
- `PrivateOriginalTarget`,
  `PrivateChoiceTaggedTarget`,
  `PrivateChoiceTaggedEdges`,
  `PrivateOriginalImageInH`,
  `PrivateOriginalTrainInH`,
  `PrivateOriginalColoursOrders`,
  `PrivateActualSingleMapAllCuts`: literal \(\tau_s\),
  original source-edge bijection, exact vertex/edge
  image, unary predicates, within-colour orders and
  one SAME physical edge map through all shifted levels.
- `PrivateActualParentStrong`,
  `PrivateCanonicalTargetStrong`,
  `PrivateActualLabelledStrong`: derive the selected
  parent's and target's strongness from old
  `OrderStage.strong`, exact complete edge range,
  and checked component-scattering strongness.

## Concrete adversarial findings

**False shortcut #1:** old physical edges being linear does NOT
imply first-wagon carriers linear. Graph edges
\(\{ab,ac,bd,cd\}\) can be partitioned into wagons
\(\{ab,ac\}\) and \(\{bd,cd\}\), whose carriers share
both \(b,c\). The actual labelled first-tail girth \(>2\)
excludes this configuration.

**False shortcut #2:** induced \(F_p\) may contain a
foreign-owned A-edge unless first-wagon carrier linearity
is used. Graph edges \(ab,ac\) in wagon zero and \(bc\)
in wagon one exhibit this failure.

**False shortcut #3:** an all-closure EHN selected-family
interface does not certify order preservation.
Keep the actual increasing selected family, and retain
its index TYPE while reblocking the \(X\)-order.

**False shortcut #4:** `ElementaryCAClass` alone
does not imply that every \(X\)-vertex is A-covered.
Use the Track 1 owner-splitting/marked restriction
to obtain the full **covered, \(S=A_1\)** ordered
Ramsey witness; mere removal of isolated X vertices
needs an actual Ramsey-arrow transfer proof.

**Typed target correction:** \(j[e]\) was not
well-defined for an untagged original T-edge.
The correct carrier is \(j[\tau_s(e)]\), and target
labels are actual pairs \((j,s)\).

The manuscript draft has been revised accordingly,
including the explicit original-vs-quotient
wagon relation calculation in the preparation lemma.

## Finite checks actually executed (not Lean proofs)

- `track5_private_smoke.py`: unequal 3/4-vertex first
  wagons, 14 template vertices, 40 filled occurrences;
  two overlapping selected old parents, 80 full
  ambient filled occurrences, exact selected edge
  carriers and complete colour words.
- `track5_quotient_tail_regression.py`: **576** random
  nested trains, all original/shortened quotient
  classes, carriers, parent squares and shifted
  allowed-part intersections; labelled girth up to
  4; actual choice-component relations, sibling
  separation and shared top.
- That regression also checked **4,218** carrier-linear
  random original edge-owner graphs: induced local
  A-support edges equal their genuinely owned edges.
  A counterexample with a foreign induced edge passed
  as a negative control.
- `track5_real_W_audit.py` (earlier check): genuine
  7-vertex unequal disjoint union with \(A_1=\{0\}\),
  5 marked coloured edges and negative controls for
  invalid marked predicates and nullary relations.

No arbitrary-colouring Ramsey theorem follows from
these bounded tests. They validate *examples and
indexing*, not the Lean proofs.

## Exact outstanding obligations

1. **Ordered W completion:** establish genuine induced F_p
   inclusions, unchanged small A-edge support,
   A-linearity and the ordered-EHN arrow for the
   COMPLETED relational W. Do not substitute the
   RAW coproduct plus an auxiliary LinearOrder.
2. **Upstream Track 1:** supply the checked owner-split,
   **covered, \(S=A_1\)-restricted, increasing selected**
   EHN Ramsey family. [Issue #1052](https://github.com/janhubicka/lean-girth/issues/1052)
   still marks this full bridge open.
3. Instantiate the original partite train \(T\)
   in its concrete coloured relational presentation
   and connect the actual quotient-tail \(M\)
   and its marked parameters to the lower
   **unrestricted ordered** \(\mathsf{RR}_{\mathbf h}\)
   stage. Do NOT impose an \(X\)-position-partite
   presentation on \(M\); only its unary-coloured
   edge type is fixed.
4. Obtain an actual **selected `OrderStage`**
   with its `DesignatedArrow` and `allCutGirth`
   from the shorter induction hypothesis.
5. Combine the same physical selected target map
   with its parts, predicates and orders and the
   checked **full** canonical H system-girth/scattering
   proof for every cut, including old equality.
6. **Kernel verification:** build each module on its exact
   branch head, then run
   `lake env lean Girth/CheckTrack5Private.lean`,
   inspect `#print axioms` and every elaborated hypothesis,
   and compile the full TeX manually.
   The active environment has no `lean`, `lake`
   or `elan` binary and no mounted mathlib build.
   GitHub Actions/TeX CI were not used as a gate.

**Status: Track 5 remains OPEN.** The complete candidate
chain is isolated on draft PR #1063; manuscript changes
remain on draft PR #450. No new validation markers
were promoted, and no merge was performed.
